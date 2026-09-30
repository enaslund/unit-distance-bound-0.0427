#!/usr/bin/env python3
"""Export the selected one-hypothesis candidate and its project import closure.

This never changes the source tree, Git index, or older submission archives.
Only public pinned dependencies are external to the resulting source archive.

Besides the exact Lean import closure, attribution and the focused submission
documentation, the archive carries three further groups of regular files:

* the source manuscript under ``docs/manuscript/``: the TeX sources,
  bibliography, Makefile, README and finished PDF from
  ``../papers/0.0418235`` in the research repository
  (its ``certificates/``, ``evidence/``, ``tools/``, ``requirements.txt`` and
  LaTeX build byproducts are not included);
* the external zeta verification records under
  ``verification/external-zeta-20260921/`` and
  ``verification/external-zeta-20260922/``, at their own relative paths;
* every existing regular file that the shipped README, NOTICE, submission
  documentation, ``third-party/`` records, or the first 40 lines of a captured
  Lean module reference by a ``verification/``, ``docs/`` or ``scripts/``
  relative path.  Brace patterns such as ``{build,audit}`` and ``*`` globs are
  expanded; the files pulled in this way are not scanned in turn (one level).

A referenced path that is not a regular file fails the export with the list of
dangling pointers, so a broken relative reference cannot ship unnoticed.  The
``--tolerate-missing-references`` flag exists only for dry runs against a
moving working tree: it records the missing paths in ``SELECTION.json`` and in
the report instead of failing.  Symlinks, Git LFS pointers and compiled
artifacts are refused everywhere.  The export is deterministic and refuses to
overwrite an existing archive or report.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile
import tomllib

from source_inventory import parse_imports

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE_ROOT = "unit-distance-zeta"

# The manuscript lives in the research repository, next to this Lean project.
MANUSCRIPT_SOURCE = Path("papers/0.0418235")
MANUSCRIPT_TARGET = "docs/manuscript"
MANUSCRIPT_FILES = ("main.tex", "references.bib", "Makefile", "README.md", "main.pdf")
MANUSCRIPT_NOT_INCLUDED = ("certificates/", "evidence/", "tools/", "requirements.txt",
                           "LaTeX build byproducts (.aux, .log, .bbl, .blg, .out, .toc, .fls)")
BUILD_BYPRODUCTS = {".aux", ".log", ".bbl", ".blg", ".out", ".toc", ".fls"}

# External zeta verification records; None means every regular file below.
EXTERNAL_ZETA_RECORDS = {
    "verification/external-zeta-20260921": ("README.md", "finite-ceiling.json", "source-and-recheck.json"),
    "verification/external-zeta-20260922": None,
}

# Shipped documents whose relative pointers must resolve inside the archive.
# The first LEAN_HEADER_LINES lines of every captured Lean module and every
# third-party/**/*.md and *.json record are scanned as well.
REFERENCE_DOCUMENTS = ("README.md", "NOTICE", "docs/CONDITIONAL_SUBMISSION.md",
                       "docs/SUBMISSION_PROVENANCE.md", "docs/PALOMAR_REPRODUCE.md")
LEAN_HEADER_LINES = 40
REFERENCE = re.compile(
    r"(?<![A-Za-z0-9_./-])((?:verification|docs|scripts)/(?:[A-Za-z0-9_./*-]|\{[A-Za-z0-9_.,*-]+\})+)")
# Palomar's own verifier entry point is cited by name in the instructions; it
# is upstream code, not a project file.  Bare file names such as GOAL.md are
# outside the pattern above and are not checked.
IGNORED_REFERENCES = frozenset({"scripts/verify_submission.py"})
# Referenced paths that may be absent without failing the export.  Keep empty;
# add a path here only with a written reason next to it.
ALLOWED_MISSING = frozenset()
REFERENCE_FILE_CAP = 5 * 1024 * 1024
REFERENCE_TOTAL_CAP = 60 * 1024 * 1024

FORBIDDEN_SUFFIXES = {".olean", ".ilean", ".ir", ".o", ".so", ".a", ".bc", ".trace", ".dll", ".dylib", ".obj"}
MODULE_SIDECARS = (".olean.private", ".olean.server", ".ir.sig")
LFS_POINTER = b"version https://git-lfs.github.com/spec/"


def canonical(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def file_record(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def imports(data):
    return parse_imports(data.decode())


def regular_file_bytes(path, label):
    """Read one regular source file; refuse symlinks, LFS pointers and artifacts."""
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Expected regular source file: {label}")
    if path.suffix in FORBIDDEN_SUFFIXES or path.name.endswith(MODULE_SIDECARS):
        raise ValueError(f"Refusing compiled artifact: {label}")
    data = path.read_bytes()
    if data.startswith(LFS_POINTER):
        raise ValueError(f"Refusing Git LFS pointer instead of file content: {label}")
    return data


def expand_braces(pattern):
    """Expand {a,b} alternatives left to right; nesting is not supported."""
    match = re.search(r"\{([^{}]*)\}", pattern)
    if not match:
        return [pattern]
    return [variant for alternative in match.group(1).split(",")
            for variant in expand_braces(pattern[:match.start()] + alternative + pattern[match.end():])]


def references(entries):
    """Map every relative pointer in the shipped documents to its referrers."""
    found = {}
    for name in sorted(entries):
        if name == "third-party/module-system-20260928/manifest.json":
            # This field records archived sources deliberately omitted from
            # the port; listing them is not a request to attach them anew.
            # Keep the manifest bytes intact, and scan all its other fields.
            record = json.loads(entries[name])
            if record.get("schema") != "unit-distance-module-port-v1":
                raise ValueError("Unexpected module-port manifest schema")
            text = json.dumps({key: value for key, value in record.items()
                               if key != "unmodified_extra_archived_lean_files"})
        elif name in REFERENCE_DOCUMENTS or (name.startswith("third-party/") and name.endswith((".md", ".json"))):
            text = entries[name].decode("utf-8", "replace")
        elif name.endswith(".lean"):
            text = b"\n".join(entries[name].splitlines()[:LEAN_HEADER_LINES]).decode("utf-8", "replace")
        else:
            continue
        for match in REFERENCE.finditer(text):
            for pointer in expand_braces(match.group(1).rstrip("./")):
                if ".." in Path(pointer).parts:
                    raise ValueError(f"Parent-directory reference in {name}: {pointer}")
                found.setdefault(pointer, set()).add(name)
    return found


def attach_references(root, entries, read, tolerate_missing):
    """Add every referenced regular file that is not already selected.

    Returns (records, missing, ignored).  A pointer already naming an archive
    member, or a directory that has archive members, needs nothing further.
    """
    found = references(entries)
    records, deferred, ignored, missing = {}, [], [], []
    total = 0
    for pointer in sorted(found):
        if pointer in IGNORED_REFERENCES:
            ignored.append(pointer)
            continue
        if pointer in entries:
            continue
        if "*" in pointer:
            targets = sorted(p.relative_to(root).as_posix() for p in root.glob(pointer)
                             if p.is_file() and not p.is_symlink())
            if not targets:
                deferred.append(pointer)
                continue
        elif (root / pointer).is_file() and not (root / pointer).is_symlink():
            targets = [pointer]
        else:
            deferred.append(pointer)
            continue
        for target in targets:
            if target in records:
                records[target]["referenced_by"] = sorted(set(records[target]["referenced_by"]) | found[pointer])
                continue
            if target in entries:
                continue
            data = read(target)
            if len(data) > REFERENCE_FILE_CAP:
                raise ValueError(f"Referenced record exceeds the 5 MiB per-file cap: {target}")
            total += len(data)
            if total > REFERENCE_TOTAL_CAP:
                raise ValueError("Referenced records exceed the 60 MiB total cap")
            records[target] = {**file_record(data), "referenced_by": sorted(found[pointer])}
    for pointer in deferred:
        # A directory pointer is satisfied by any archive member below it.
        if not any(name.startswith(pointer + "/") for name in entries):
            missing.append(pointer)
    missing = sorted(set(missing) - ALLOWED_MISSING)
    if missing and not tolerate_missing:
        raise ValueError("Referenced paths are not regular files; fix the pointers or add the "
                         "files before exporting:\n  " + "\n  ".join(
                             f"{pointer} <- {', '.join(sorted(found[pointer]))}" for pointer in missing))
    return records, missing, ignored


def capture(root, tolerate_missing=False):
    root = Path(root)
    if (root / "SOURCE_SNAPSHOT.json").is_file():
        snapshot = json.loads((root / "SOURCE_SNAPSHOT.json").read_text())
        sealed = {}
        for name, expected in snapshot.items():
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError(f"Invalid snapshot member: {name}")
            path = root / relative
            if path.is_symlink() or not path.is_file():
                raise ValueError(f"Missing regular snapshot member: {name}")
            data = path.read_bytes()
            if file_record(data) != expected:
                raise ValueError(f"Sealed snapshot member changed: {name}")
            sealed[name] = data
        return sealed, json.loads(sealed["SELECTION.json"])["source_origins"]
    entries = {}
    origins = {}

    def read(source, target=None):
        data = regular_file_bytes(root / source, source)
        entries[target or source] = data
        origins[source] = file_record(data)
        return data

    config = json.loads(read("comparator-zeta.json"))
    if config["challenge_module"] != "ChallengeZeta" or config["solution_module"] != "SolutionZeta":
        raise ValueError("Unexpected selected modules")
    if set(config["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("Unexpected axiom policy")
    if config.get("enable_nanoda") is not True:
        raise ValueError("NanoDa must be enabled")
    pending = ["ChallengeZeta", "SolutionZeta", "AuditSupport"]
    modules = set()
    external = set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        source = module.replace(".", "/") + ".lean"
        data = read(source)
        modules.add(module)
        for imported in imports(data):
            if (root / (imported.replace(".", "/") + ".lean")).is_file():
                pending.append(imported)
            else:
                if imported == "UnitDistance" or imported.startswith("UnitDistance."):
                    raise ValueError(f"Missing project import {imported} in {source}")
                external.add(imported)
    challenge_imports = list(imports(entries["ChallengeZeta.lean"]))
    if not challenge_imports or not all(m == "Mathlib" or m.startswith("Mathlib.")
                                        for m in challenge_imports):
        raise ValueError("Challenge direct imports must be canonical Mathlib modules")
    if len(entries["ChallengeZeta.lean"]) > 100 * 1024 or len(entries["ChallengeZeta.lean"].splitlines()) > 1000:
        raise ValueError("Challenge exceeds inspected policy caps")
    original_lake = tomllib.loads(read("lakefile.toml").decode())
    requirements = original_lake["require"]
    if len(requirements) != 1 or requirements[0]["name"] != "mathlib":
        raise ValueError("Review new Lake dependencies before exporting")
    req = requirements[0]
    if not re.fullmatch(r"[0-9a-f]{40}", req["rev"]):
        raise ValueError("Mathlib must be pinned to a full commit")
    entries["lakefile.toml"] = (
        'name = "unitDistance"\nversion = "0.1.0"\n'
        'defaultTargets = ["SolutionZeta", "ChallengeZeta"]\n\n'
        '[[require]]\nname = "mathlib"\n'
        f'git = "{req["git"]}"\nrev = "{req["rev"]}"\n\n'
        + "\n".join(f'[[lean_lib]]\nname = "{m}"\n'
                      for m in ("UnitDistance", "ChallengeZeta", "SolutionZeta", "AuditSupport"))
    ).encode()
    entries["UnitDistance.lean"] = b"module\npublic import SolutionZeta\n"
    for name in ("LICENSE", "NOTICE", "lean-toolchain", "lake-manifest.json"):
        read(name)
    read("README-zeta.md", "README.md")
    read("formalization-zeta.yaml", "formalization.yaml")
    read("verification/ZetaAudit.lean")
    read("scripts/check-metadata.py")
    read("scripts/export-zeta-candidate.py")
    read("scripts/source_inventory.py")
    read("scripts/module_port_provenance.py")
    read("scripts/verify-zeta-candidate.py")
    read("scripts/verify-palomar-local.py")
    read("scripts/setup-verification-tools.sh")
    for name in ("CONDITIONAL_SUBMISSION.md", "SUBMISSION_PROVENANCE.md", "PALOMAR_REPRODUCE.md"):
        read("docs/" + name)
    # Preserve attribution for the entire port slices, even where the selected
    # proof imports only a subset. Historical research/status documents stay in
    # the research repository and in the already sealed older archives.
    for folder in ("third-party",):
        for path in sorted((root / folder).rglob("*")):
            if path.is_file():
                if any(part in {".git", ".lake", ".cache", "__pycache__"}
                       for part in path.relative_to(root).parts):
                    raise ValueError(f"Unexpected generated source under {folder}: {path}")
                read(path.relative_to(root).as_posix())
    # The manuscript: a curated list, read from the research repository.
    manuscript_dir = root.parent / MANUSCRIPT_SOURCE
    manuscript = {}

    def read_manuscript(relative):
        origin = MANUSCRIPT_SOURCE / relative
        data = regular_file_bytes(manuscript_dir / relative, f"manuscript file {origin.as_posix()}")
        entries[f"{MANUSCRIPT_TARGET}/{relative}"] = data
        manuscript[f"{MANUSCRIPT_TARGET}/{relative}"] = {"origin": origin.as_posix(), **file_record(data)}

    for name in MANUSCRIPT_FILES:
        read_manuscript(name)
    for path in sorted((manuscript_dir / "sections").iterdir()):
        if path.suffix == ".tex":
            read_manuscript(f"sections/{path.name}")
        elif path.suffix not in BUILD_BYPRODUCTS:
            raise ValueError(f"Unexpected non-TeX manuscript section file: {path.name}")
    # External zeta verification records, at their own relative paths.
    external_records = []
    for folder, names in EXTERNAL_ZETA_RECORDS.items():
        if names is None:
            names = sorted(p.relative_to(root / folder).as_posix() for p in (root / folder).rglob("*")
                           if p.is_file())
            if not names:
                raise ValueError(f"No regular files under {folder}")
        for name in names:
            if any(part.startswith(".") or part == "__pycache__" for part in Path(name).parts):
                raise ValueError(f"Unexpected hidden or generated record under {folder}: {name}")
            read(f"{folder}/{name}")
            external_records.append(f"{folder}/{name}")
    # Every regular file the shipped documents point at by relative path.
    records, missing, ignored = attach_references(root, entries, read, tolerate_missing)
    entries[".gitignore"] = b".lake/\n.cache/\n.toolchain/\ndist/\n"
    entries["SELECTION.json"] = canonical({
        "schema": "unit-distance-selected-candidate-v2",
        "comparator": "comparator-zeta.json",
        "project_modules": sorted(modules),
        "external_direct_imports": sorted(external),
        "challenge_direct_imports": challenge_imports,
        "source_origins": origins,
        "generated_files": ["lakefile.toml", "UnitDistance.lean", ".gitignore"],
        "manuscript_origin": (f"{MANUSCRIPT_SOURCE.as_posix()} in the research repository, the parent "
                              "directory of this Lean project; origins below are relative to that root"),
        "manuscript_not_included": list(MANUSCRIPT_NOT_INCLUDED),
        "manuscript_files": manuscript,
        "external_zeta_records": external_records,
        "referenced_records": records,
        "references_ignored": ignored,
        "missing_references": missing,
        "scope": ("One selected conditional candidate: the exact project import closure and attribution; "
                  "the source manuscript under docs/manuscript; the external zeta verification records; "
                  "and every regular file that the shipped documentation, third-party records or captured "
                  "module headers reference by a verification/, docs/ or scripts/ relative path. "
                  "Dependencies, build artifacts and other research data are not included. "
                  "No remote submission."),
    })
    return entries, origins


def write_archive(entries, output):
    snapshot = {name: file_record(data) for name, data in sorted(entries.items())}
    payload = dict(entries)
    payload["SOURCE_SNAPSHOT.json"] = canonical(snapshot)
    source_bytes = sum(map(len, payload.values()))
    if source_bytes > 500 * 1024 * 1024:
        raise ValueError("Source snapshot exceeds 500 MiB")
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("xb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for name, data in sorted(payload.items()):
                    member = tarfile.TarInfo(f"{ARCHIVE_ROOT}/{name}")
                    member.size = len(data)
                    member.mode = 0o755 if name.startswith("scripts/") else 0o644
                    member.mtime = 0
                    archive.addfile(member, io.BytesIO(data))
    return {"archive": str(output), "archive_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
            "archive_bytes": output.stat().st_size, "source_bytes": source_bytes,
            "files": len(payload), "snapshot_sha256": hashlib.sha256(canonical(snapshot)).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--tolerate-missing-references", action="store_true",
                        help="Dry runs only: record referenced paths that are not regular files in "
                             "SELECTION.json and the report instead of failing the export")
    args = parser.parse_args()
    if args.output.exists() or args.report.exists():
        raise SystemExit("Refusing to overwrite an earlier archive or report")
    entries, origins = capture(ROOT, args.tolerate_missing_references)
    entries2, origins2 = capture(ROOT, args.tolerate_missing_references)
    if entries2 != entries or origins2 != origins:
        raise SystemExit("Selected sources changed during capture; retry")
    result = write_archive(entries, args.output.resolve())
    selection = json.loads(entries["SELECTION.json"])
    result.update(project_modules=len(selection["project_modules"]),
                  manuscript_files=len(selection["manuscript_files"]),
                  external_zeta_records=len(selection["external_zeta_records"]),
                  referenced_records=len(selection["referenced_records"]),
                  references_ignored=selection["references_ignored"],
                  missing_references=selection["missing_references"],
                  missing_references_tolerated=args.tolerate_missing_references,
                  selected_configuration="comparator-zeta.json", proof_verification_performed=False,
                  remote_submission=False)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_bytes(canonical(result))
    print(canonical(result).decode(), end="")
    if selection["missing_references"]:
        print("WARNING: missing referenced paths were tolerated; this archive is a dry run, not a candidate:")
        for pointer in selection["missing_references"]:
            print("  " + pointer)


if __name__ == "__main__":
    main()

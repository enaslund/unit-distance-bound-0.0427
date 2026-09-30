#!/usr/bin/env python3
"""Export the exact conditional 1.0427 theorem over Q(sqrt 241).

The selected roots are ChallengeZeta241, SolutionZeta241 and AuditSupport.
The comparator must select exactly the independently stated genus-field
theorem. The earlier conditional theorem at exponent 2083647/2000000
(ChallengeZeta, SolutionZeta, comparator-zeta.json) is shipped beside it as an
unselected companion, with its import closure, metadata, README, axiom audit
and external evidence records; the generated lakefile declares its libraries,
and the default build targets remain the selected theorem. No build, external numerical replay, remote action or source edit is
performed. Existing archives and reports are never overwritten.

The established exporter supplies the regular-file checks, import parser,
reference attachment, canonical JSON, sealed-snapshot reader and deterministic
archive writer. This script supplies its own explicit theorem selection and
source mapping; it never invokes the older theorem's unsealed capture path.
SOURCE_SNAPSHOT.json and SELECTION.json keep the established schemas. The
archive root remains unit-distance-zeta for the family's extraction contract;
the comparator and exporter names inside it identify the 241 theorem.

The original manuscript is preserved under docs/manuscript and the new
research-note sources/evidence under docs/quadratic-base-research. These are
provenance copies: the external computation still expects the original
research repository and manuscript supplementary archive. It is not part of
the Lean proof or this export's verification claim.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import tomllib


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "_zeta241_archive_support", Path(__file__).with_name("export-zeta-candidate.py"))
SUPPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SUPPORT)

COMPARATOR = "comparator-zeta241.json"
EXPORTER = "scripts/export-zeta241-candidate.py"
CHALLENGE = "ChallengeZeta241"
SOLUTION = "SolutionZeta241"
THEOREM = "UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound"
ROOT_MODULES = (CHALLENGE, SOLUTION, "AuditSupport")
# The earlier theorem ships as an unselected companion; most of its import
# closure is shared with the selected theorem.
COMPANION_COMPARATOR = "comparator-zeta.json"
COMPANION_CHALLENGE = "ChallengeZeta"
COMPANION_SOLUTION = "SolutionZeta"
COMPANION_THEOREM = "UnitDistanceZetaSubmission.target_of_canonical_zeta_bound"
COMPANION_ROOTS = (COMPANION_CHALLENGE, COMPANION_SOLUTION)
COMPANION_FILES = ("formalization-zeta.yaml", "README-zeta.md", "verification/ZetaAudit.lean")
LEAN_LIBRARIES = ("UnitDistance", *ROOT_MODULES, *COMPANION_ROOTS)
AUDIT = "verification/Zeta241Audit.lean"
RESEARCH_SOURCE = Path("papers/0.04273")
RESEARCH_TARGET = "docs/quadratic-base-research"
VERIFICATION_RECORDS = "verification/sqrt241-20260929"
SOURCE_MAP = {
    "README-zeta241.md": "README.md",
    "formalization-zeta241.yaml": "formalization.yaml",
}
REQUIRED_FILES = (
    "LICENSE", "NOTICE", "lean-toolchain", "lake-manifest.json",
    "scripts/check-metadata.py", EXPORTER, "scripts/export-zeta-candidate.py",
    "scripts/source_inventory.py", "scripts/module_port_provenance.py",
    "scripts/verify-zeta-candidate.py", "scripts/verify-palomar-local.py",
    "scripts/setup-verification-tools.sh", "scripts/verify_palomar_bounded.py",
    "scripts/verify_palomar_host.py",
    "docs/SQRT241_PORT.md", "docs/SUBMISSION_PROVENANCE.md",
    "docs/PALOMAR_REPRODUCE.md", "docs/CONDITIONAL_SUBMISSION.md",
    "certificates/finite-witness-241.json",
)
SKIPPED_RESEARCH_PARTS = {".git", ".cache", "__pycache__", ".gitignore"}
# This historical plan names a proposed generator, not a delivered artifact.
# The delivered generators are listed in SUBMISSION.md and shipped in full.
# Exclude only this referrer; an active document using the same path still
# fails the ordinary missing-reference check.
HISTORICAL_PLANNED_REFERENCES = {
    "scripts/sqrt241/generate_tower_certificates.py": ["docs/sqrt241/TOWER_PLAN.md"],
}

AUDIT_SOURCE = b"""module

public import SolutionZeta241
public meta import AuditSupport

@[expose] public section
set_option backward.privateInPublic true

set_option maxHeartbeats 0
run_cmd UnitDistanceAudit.audit `UnitDistance
run_cmd UnitDistanceAudit.audit `UnitDistanceSqrt241Submission

#print axioms UnitDistance.Sqrt241.target_of_canonical_genus_zeta_bound
#print axioms UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound
"""

# Scan all current 241 notes in addition to inherited provenance. Referenced
# records are attached only one level deep, as in the established exporter.
SUPPORT.REFERENCE_DOCUMENTS += ("formalization.yaml", "docs/SQRT241_PORT.md")


def validate_config(config, challenge=CHALLENGE, solution=SOLUTION, theorem=THEOREM):
    """Fail closed on both the module pair and the declaration selector."""
    if (config.get("challenge_module") != challenge
            or config.get("solution_module") != solution):
        raise ValueError(f"Unexpected selected modules: expected {challenge}/{solution}")
    if config.get("theorem_names") != [theorem] or config.get("definition_names") != []:
        raise ValueError(f"Unexpected selected theorem or definitions for {solution}")
    if (not isinstance(config.get("permitted_axioms"), list)
            or sorted(config["permitted_axioms"]) != sorted(["propext", "Quot.sound", "Classical.choice"])):
        raise ValueError("Unexpected axiom policy")
    if config.get("enable_nanoda") is not True:
        raise ValueError("NanoDa must be enabled")


def module_closure(roots, read, present):
    """Read precisely the local import closure of the given roots."""
    pending = list(roots)
    modules, external = set(), set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        source = module.replace(".", "/") + ".lean"
        data = read(source)
        modules.add(module)
        for imported in SUPPORT.imports(data):
            path = imported.replace(".", "/") + ".lean"
            if present(path):
                pending.append(imported)
            elif imported == "UnitDistance" or imported.startswith("UnitDistance."):
                raise ValueError(f"Missing project import {imported} in {source}")
            else:
                external.add(imported)
    return modules, external


def project_closure(read, present):
    """Read precisely the local import closure of the three selected roots."""
    modules, external = module_closure(ROOT_MODULES, read, present)
    if modules & {"UnitDistance", "ChallengeZeta", "SolutionZeta"}:
        raise ValueError("Selected closure imports a legacy target or the generated umbrella")
    return sorted(modules), sorted(external)


def companion_closure(read, present, selected):
    """Read the companion theorem's closure; return its modules beyond the selected closure."""
    modules, external = module_closure(COMPANION_ROOTS, read, present)
    if modules & {"UnitDistance", CHALLENGE, SOLUTION}:
        raise ValueError("Companion closure imports the selected theorem or the generated umbrella")
    return sorted(modules - set(selected)), sorted(external)


def validate_companion_challenge(data):
    imports = list(SUPPORT.imports(data))
    if not imports or not all(m == "Mathlib" or m.startswith("Mathlib.") for m in imports):
        raise ValueError("Companion challenge direct imports must be canonical Mathlib modules")


def validate_selection(entries):
    """Also enforce the target contract when re-exporting a sealed archive."""
    selection = json.loads(entries["SELECTION.json"])
    if (selection.get("schema") != "unit-distance-selected-candidate-v2"
            or selection.get("comparator") != COMPARATOR
            or selection.get("exporter") != EXPORTER):
        raise ValueError("Unexpected sealed 241 selection")
    validate_config(json.loads(entries[COMPARATOR]))
    modules, external = project_closure(entries.__getitem__, entries.__contains__)
    if (selection.get("project_modules") != modules
            or selection.get("external_direct_imports") != external):
        raise ValueError("Selected import closure differs from captured sources")
    lake = tomllib.loads(entries["lakefile.toml"].decode())
    if lake.get("defaultTargets") != [SOLUTION, CHALLENGE]:
        raise ValueError("Unexpected default build targets")
    if [library.get("name") for library in lake.get("lean_lib", [])] != list(LEAN_LIBRARIES):
        raise ValueError("Unexpected Lake libraries")
    validate_config(json.loads(entries[COMPANION_COMPARATOR]),
                    COMPANION_CHALLENGE, COMPANION_SOLUTION, COMPANION_THEOREM)
    validate_companion_challenge(entries[f"{COMPANION_CHALLENGE}.lean"])
    beyond, companion_external = companion_closure(entries.__getitem__, entries.__contains__, modules)
    companion = selection.get("companion_theorem") or {}
    if (companion.get("comparator") != COMPANION_COMPARATOR
            or companion.get("theorem") != COMPANION_THEOREM
            or companion.get("modules_beyond_selected") != beyond
            or companion.get("external_direct_imports") != companion_external):
        raise ValueError("Companion theorem differs from captured sources")
    for name in COMPANION_FILES:
        if name not in entries:
            raise ValueError(f"Missing companion file {name}")
    if entries["UnitDistance.lean"] != f"module\npublic import {SOLUTION}\n".encode():
        raise ValueError("Unexpected generated umbrella")
    if entries[AUDIT] != AUDIT_SOURCE:
        raise ValueError("Unexpected generated 241 axiom audit")
    return selection


def capture(root, tolerate_missing=False):
    root = Path(root)
    if (root / "SOURCE_SNAPSHOT.json").is_file():
        # The support capture returns before the old, hardcoded source
        # selection when SOURCE_SNAPSHOT.json is present.
        entries, origins = SUPPORT.capture(root, tolerate_missing)
        validate_selection(entries)
        return entries, origins

    entries, origins, source_mapping = {}, {}, {}

    def read(source, target=None):
        data = SUPPORT.regular_file_bytes(root / source, source)
        target = target or source
        entries[target] = data
        origins[source] = SUPPORT.file_record(data)
        source_mapping[target] = source
        return data

    validate_config(json.loads(read(COMPARATOR)))
    modules, external = project_closure(read, lambda p: (root / p).is_file())
    challenge_data = entries[f"{CHALLENGE}.lean"]
    challenge_imports = list(SUPPORT.imports(challenge_data))
    if not challenge_imports or not all(m == "Mathlib" or m.startswith("Mathlib.")
                                        for m in challenge_imports):
        raise ValueError("Challenge direct imports must be canonical Mathlib modules")
    if len(challenge_data) > 100 * 1024 or len(challenge_data.splitlines()) > 1000:
        raise ValueError("Challenge exceeds inspected policy caps")
    validate_config(json.loads(read(COMPANION_COMPARATOR)),
                    COMPANION_CHALLENGE, COMPANION_SOLUTION, COMPANION_THEOREM)
    companion_modules, companion_external = companion_closure(
        read, lambda p: (root / p).is_file(), modules)
    validate_companion_challenge(entries[f"{COMPANION_CHALLENGE}.lean"])
    lake = tomllib.loads(read("lakefile.toml").decode())
    requirements = lake["require"]
    if len(requirements) != 1 or requirements[0]["name"] != "mathlib":
        raise ValueError("Review new Lake dependencies before exporting")
    req = requirements[0]
    if not re.fullmatch(r"[0-9a-f]{40}", req["rev"]):
        raise ValueError("Mathlib must be pinned to a full commit")
    entries["lakefile.toml"] = (
        'name = "unitDistance"\nversion = "0.1.0"\n'
        f'defaultTargets = ["{SOLUTION}", "{CHALLENGE}"]\n\n'
        '[[require]]\nname = "mathlib"\n'
        f'git = "{req["git"]}"\nrev = "{req["rev"]}"\n\n'
        + "\n".join(f'[[lean_lib]]\nname = "{m}"\n'
                      for m in LEAN_LIBRARIES)
    ).encode()
    entries["UnitDistance.lean"] = f"module\npublic import {SOLUTION}\n".encode()
    entries[AUDIT] = AUDIT_SOURCE
    for source, target in SOURCE_MAP.items():
        read(source, target)
    for name in REQUIRED_FILES:
        read(name)
    for name in COMPANION_FILES:
        read(name)
    # The companion's external evidence, at its own relative paths.
    for folder, names in SUPPORT.EXTERNAL_ZETA_RECORDS.items():
        if names is None:
            names = sorted(p.relative_to(root / folder).as_posix() for p in (root / folder).rglob("*")
                           if p.is_file())
            if not names:
                raise ValueError(f"No regular files under {folder}")
        for name in names:
            if any(part.startswith(".") or part == "__pycache__" for part in Path(name).parts):
                raise ValueError(f"Unexpected hidden or generated record under {folder}: {name}")
            read(f"{folder}/{name}")

    for folder in ("third-party", "docs/sqrt241", "scripts/sqrt241", VERIFICATION_RECORDS):
        paths = sorted((root / folder).rglob("*"))
        if not any(p.is_file() for p in paths):
            raise ValueError(f"No regular sources under {folder}")
        for path in paths:
            if path.is_symlink():
                raise ValueError(f"Refusing source symlink: {path.relative_to(root)}")
            if not path.is_file():
                continue
            relative = path.relative_to(root)
            if any(part in {".git", ".lake", ".cache", "__pycache__"}
                   for part in relative.parts):
                raise ValueError(f"Unexpected generated source under {folder}: {relative}")
            read(relative.as_posix())
    current_docs = tuple(name for name in entries if name.startswith("docs/sqrt241/") and name.endswith(".md"))

    manuscript = {}
    manuscript_dir = root.parent / SUPPORT.MANUSCRIPT_SOURCE

    def read_manuscript(relative):
        origin = SUPPORT.MANUSCRIPT_SOURCE / relative
        target = f"{SUPPORT.MANUSCRIPT_TARGET}/{relative}"
        data = SUPPORT.regular_file_bytes(manuscript_dir / relative, origin.as_posix())
        entries[target] = data
        manuscript[target] = {"origin": origin.as_posix(), **SUPPORT.file_record(data)}

    for name in SUPPORT.MANUSCRIPT_FILES:
        read_manuscript(name)
    for path in sorted((manuscript_dir / "sections").iterdir()):
        if path.suffix == ".tex":
            read_manuscript(f"sections/{path.name}")
        elif path.suffix not in SUPPORT.BUILD_BYPRODUCTS:
            raise ValueError(f"Unexpected non-TeX manuscript section file: {path.name}")

    research = {}
    research_dir = root.parent / RESEARCH_SOURCE
    for path in sorted(research_dir.rglob("*")):
        relative = path.relative_to(research_dir)
        if any(part in SKIPPED_RESEARCH_PARTS for part in relative.parts):
            continue
        if path.is_symlink():
            raise ValueError(f"Refusing research symlink: {relative}")
        if not path.is_file():
            continue
        origin = RESEARCH_SOURCE / relative
        data = SUPPORT.regular_file_bytes(path, origin.as_posix())
        target = f"{RESEARCH_TARGET}/{relative.as_posix()}"
        entries[target] = data
        research[target] = {"origin": origin.as_posix(), **SUPPORT.file_record(data)}
    for required in ("README.md", "research/construction.md", "certificates/h241_receipt.json",
                     "certificates/reproduce241.py", "certificates/env241.py"):
        if f"{RESEARCH_TARGET}/{required}" not in research:
            raise ValueError(f"Missing quadratic-base research source: {required}")

    previous_docs = SUPPORT.REFERENCE_DOCUMENTS
    previous_references = SUPPORT.references

    def current_references(payload):
        found = previous_references(payload)
        for pointer, referrers in HISTORICAL_PLANNED_REFERENCES.items():
            if pointer in found:
                found[pointer] -= set(referrers)
                if not found[pointer]:
                    del found[pointer]
        return found

    try:
        SUPPORT.REFERENCE_DOCUMENTS += current_docs + ("README-zeta.md",)
        SUPPORT.references = current_references
        records, missing, ignored = SUPPORT.attach_references(root, entries, read, tolerate_missing)
    finally:
        SUPPORT.REFERENCE_DOCUMENTS = previous_docs
        SUPPORT.references = previous_references
    entries[".gitignore"] = b".lake/\n.cache/\n.toolchain/\ndist/\n"
    entries["SELECTION.json"] = SUPPORT.canonical({
        "schema": "unit-distance-selected-candidate-v2",
        "comparator": COMPARATOR,
        "exporter": EXPORTER,
        "project_modules": modules,
        "external_direct_imports": external,
        "challenge_direct_imports": challenge_imports,
        "companion_theorem": {
            "comparator": COMPANION_COMPARATOR,
            "theorem": COMPANION_THEOREM,
            "modules_beyond_selected": companion_modules,
            "external_direct_imports": companion_external,
            "files": list(COMPANION_FILES),
            "role": ("Unselected earlier conditional theorem at exponent 2083647/2000000, shipped for "
                     "reference; lake build SolutionZeta ChallengeZeta builds it."),
        },
        "source_origins": origins,
        "source_mapping": source_mapping,
        "generated_files": ["lakefile.toml", "UnitDistance.lean", AUDIT, ".gitignore"],
        "manuscript_origin": f"{SUPPORT.MANUSCRIPT_SOURCE.as_posix()} in the research repository",
        "manuscript_not_included": list(SUPPORT.MANUSCRIPT_NOT_INCLUDED),
        # Keep all inputs originating outside the Lean project in the
        # established origin-bearing map, so Git-only reconstruction can
        # bind both the manuscript and the research note without a new schema.
        "manuscript_files": {**manuscript, **research},
        "research_note_origin": RESEARCH_SOURCE.as_posix(),
        "research_note_files": research,
        "research_note_not_included": sorted(SKIPPED_RESEARCH_PARTS),
        "research_note_replay_scope": (
            "Sources and recorded evidence only. External numerical replay requires the original "
            "research-repository layout, manuscript supplementary archive and numerical tools; "
            "it is not a Lean proof dependency or performed by this exporter."),
        "external_zeta_records": sorted(name for name in research if "/certificates/" in name),
        "verification_records": sorted(name for name in entries if name.startswith(VERIFICATION_RECORDS + "/")),
        "referenced_records": records,
        "references_ignored": ignored,
        "historical_planned_references": HISTORICAL_PLANNED_REFERENCES,
        "missing_references": missing,
        "scope": (
            "The exact local import closure of ChallengeZeta241, SolutionZeta241 and AuditSupport; "
            "one selected conditional theorem at exponent 10427/10000. The earlier conditional theorem "
            "at exponent 2083647/2000000 is included as an unselected companion with its import closure, "
            "metadata, README, axiom audit and external evidence records. Attribution, source manuscript, "
            "quadratic-base research sources/evidence, 241 generators and their input, historical "
            "verification receipts and one-level referenced records are included. Dependencies and "
            "compiled artifacts are external. No proof verification or remote submission is performed."),
    })
    validate_selection(entries)
    return entries, origins


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--tolerate-missing-references", action="store_true", help="Dry runs only")
    args = parser.parse_args()
    if args.output.exists() or args.report.exists() or args.output.resolve() == args.report.resolve():
        raise SystemExit("Refusing to overwrite an earlier archive or report")
    entries, origins = capture(ROOT, args.tolerate_missing_references)
    entries2, origins2 = capture(ROOT, args.tolerate_missing_references)
    if entries2 != entries or origins2 != origins:
        raise SystemExit("Selected sources changed during capture; retry")
    result = SUPPORT.write_archive(entries, args.output.resolve())
    selection = validate_selection(entries)
    result.update(
        project_modules=len(selection["project_modules"]),
        companion_modules_beyond_selected=len(selection["companion_theorem"]["modules_beyond_selected"]),
        manuscript_files=len(selection["manuscript_files"]),
        research_note_files=len(selection["research_note_files"]),
        external_zeta_records=len(selection["external_zeta_records"]),
        referenced_records=len(selection["referenced_records"]),
        references_ignored=selection["references_ignored"],
        historical_planned_references=selection["historical_planned_references"],
        missing_references=selection["missing_references"],
        missing_references_tolerated=args.tolerate_missing_references,
        selected_configuration=COMPARATOR, selected_theorem=THEOREM,
        proof_verification_performed=False, remote_submission=False)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    with args.report.open("xb") as report:
        report.write(SUPPORT.canonical(result))
    print(SUPPORT.canonical(result).decode(), end="")
    if selection["missing_references"]:
        print("WARNING: missing references were tolerated; this is a dry run, not a candidate:")
        for pointer in selection["missing_references"]:
            print("  " + pointer)


if __name__ == "__main__":
    main()

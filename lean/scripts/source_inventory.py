#!/usr/bin/env python3
"""Map working-tree Lean source imports without invoking Lean or reading caches.

This is a navigation tool, not a Lean parser, build, or theorem audit. Import
recognition follows the pinned Lean 4.35 module header grammar. Paths determine
source categories; reachability alone does not determine a source's usefulness.
"""

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
import tomllib
import unicodedata


ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_DIRS = {".git", ".lake", ".cache", ".toolchain", "dist", "__pycache__"}
EXTERNAL_PREFIXES = {
    "Init", "Lean", "Lake", "Std", "Mathlib", "Aesop", "Batteries", "Qq",
    "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible", "Cli",
}
AUDIT_CHECKS = {
    "CheckDyadic", "CheckDyadicFox", "CheckDyadicGraded", "CheckDyadicPBW",
    "CheckGroupAlgebraCosets",
}
HEADER_KEYWORDS = {"module", "prelude", "public", "meta", "import", "all"}


def _ident_start(char):
    return char == "_" or char.isalpha()


def _ident_rest(char):
    return (_ident_start(char) or char.isdigit() or char == "'"
            or unicodedata.category(char) in {"Mn", "Mc", "Nl", "No"})


def module_name(parts):
    """Render path components as module identifiers, retaining escaped dots."""
    return ".".join(
        part if part and _ident_start(part[0]) and all(map(_ident_rest, part[1:]))
        and part not in HEADER_KEYWORDS else f"«{part}»"
        for part in parts)


class _HeaderLexer:
    """Read only the header: comments nest, and quoted names are indivisible."""

    def __init__(self, source):
        self.source = source
        self.pos = int(source.startswith("\ufeff"))

    def _skip_space(self):
        source = self.source
        while self.pos < len(source):
            if source[self.pos].isspace():
                self.pos += 1
            elif source.startswith("--", self.pos):
                end = source.find("\n", self.pos)
                self.pos = len(source) if end < 0 else end + 1
            elif source.startswith("/-", self.pos):
                start = self.pos
                self.pos += 2
                depth = 1
                while depth:
                    opening = source.find("/-", self.pos)
                    closing = source.find("-/", self.pos)
                    if closing < 0:
                        line = source.count("\n", 0, start) + 1
                        raise ValueError(f"unterminated header comment at line {line}")
                    if 0 <= opening < closing:
                        depth += 1
                        self.pos = opening + 2
                    else:
                        depth -= 1
                        self.pos = closing + 2
            else:
                break

    def token(self):
        """Return (literal spelling, normalized module name or None)."""
        self._skip_space()
        source = self.source
        start = self.pos
        if start == len(source):
            return "", None
        parts = []
        while self.pos < len(source):
            if source[self.pos] == "«":
                end = source.find("»", self.pos + 1)
                if end < 0:
                    raise ValueError("unterminated escaped identifier in header")
                parts.append(source[self.pos + 1:end])
                self.pos = end + 1
            elif _ident_start(source[self.pos]):
                begin = self.pos
                self.pos += 1
                while self.pos < len(source) and _ident_rest(source[self.pos]):
                    self.pos += 1
                parts.append(source[begin:self.pos])
            else:
                if parts:
                    raise ValueError("incomplete dotted module identifier in header")
                self.pos += 1
                return source[start:self.pos], None
            if self.pos == len(source) or source[self.pos] != ".":
                break
            self.pos += 1
            if self.pos == len(source):
                raise ValueError("incomplete dotted module identifier in header")
        return source[start:self.pos], module_name(parts)


def parse_header(source):
    """Return (explicit imports, import-only source); reject bad header tokens.

    Recognizes `module`, `prelude`, and `[public] [meta] import [all] Name`,
    including multiline directives, nested comments, and escaped identifiers.
    Stops at the first non-header command; quoted imports and examples in the
    body are never scanned. Implicit Init imports and elaboration are outside
    scope. An import-only source contains no body token after its header and
    comments. The result does not certify header or body validity in Lean.
    """
    lexer = _HeaderLexer(source)
    token = lexer.token()
    if token[0] == "module":
        token = lexer.token()
    if token[0] == "prelude":
        token = lexer.token()
    imports = []
    while True:
        modifier = False
        if token[0] == "public":
            modifier = True
            token = lexer.token()
        if token[0] == "meta":
            modifier = True
            token = lexer.token()
        if token[0] != "import":
            return imports, not token[0] and not modifier
        token = lexer.token()
        if token[0] == "all":
            token = lexer.token()
        if token[1] is None or token[0] in HEADER_KEYWORDS:
            raise ValueError(f"expected module identifier after import, found {token[0]!r}")
        imports.append(token[1])
        token = lexer.token()


def parse_imports(source):
    """Return explicit header imports in order, including repetitions."""
    return parse_header(source)[0]


def classify(path):
    parts = path.parts
    if parts[:2] == ("research", "scratch"):
        return "scratch"
    if parts[0] == "research":
        return "research"
    if parts[0] in {"verification", "reviews"}:
        return "verification"
    if parts[:2] == ("UnitDistance", "Upstream"):
        return "upstream"
    if parts[:2] == ("UnitDistance", "ThirdParty") or parts[0] == "third-party":
        return "third-party"
    if parts[0] == "UnitDistance" or path.as_posix() == "UnitDistance.lean":
        return "project-library"
    if len(parts) == 1:
        if path.stem.startswith(("Challenge", "Solution")):
            return "wrapper"
        if path.stem.startswith("Audit") or path.stem in AUDIT_CHECKS:
            return "verification"
        if path.stem.startswith(("Check", "Scratch")):
            return "scratch"
    return "other"


def source_paths(root):
    paths, symlinks = [], []
    for directory, subdirs, filenames in os.walk(root, followlinks=False):
        base = Path(directory)
        kept = []
        for name in sorted(subdirs):
            path = base / name
            if name in EXCLUDED_DIRS:
                continue
            if path.is_symlink():
                symlinks.append(path.relative_to(root).as_posix())
            else:
                kept.append(name)
        subdirs[:] = kept
        for name in sorted(filenames):
            path = base / name
            if path.suffix == ".lean":
                if path.is_symlink():
                    symlinks.append(path.relative_to(root).as_posix())
                else:
                    paths.append(path)
    return sorted(paths), sorted(symlinks)


def lake_roots(root):
    """Read this project's conventional source layout, without running Lake."""
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    libraries = {}
    for library in config.get("lean_lib", []):
        if library.get("srcDir", ".") != ".":
            raise ValueError("source inventory does not support custom lean_lib srcDir")
        libraries[library["name"]] = library.get("roots", [library["name"]])
    defaults = set()
    for target in config.get("defaultTargets", []):
        name = target.split(":", 1)[0]
        defaults.update(libraries.get(name, [name]))
    configured = sorted({name for roots in libraries.values() for name in roots})
    return sorted(defaults), configured


def closure(modules, roots):
    reached, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in modules and name not in reached:
            reached.add(name)
            pending.extend(modules[name]["local_imports"])
    return reached


def local_import_cycles(modules):
    """Return cyclic strongly connected components, without recursive DFS.

    Iterative traversal also handles generated chains deeper than Python's
    recursion limit. A singleton is cyclic only when it imports itself.
    """
    visited, finished = set(), []
    for start in sorted(modules):
        pending = [(start, False)]
        while pending:
            name, expanded = pending.pop()
            if expanded:
                finished.append(name)
            elif name not in visited:
                visited.add(name)
                pending.append((name, True))
                pending.extend((dep, False) for dep in
                               reversed(modules[name]["local_imports"]) if dep not in visited)
    visited, cycles = set(), []
    for start in reversed(finished):
        if start in visited:
            continue
        component, pending = [], [start]
        while pending:
            name = pending.pop()
            if name not in visited:
                visited.add(name)
                component.append(name)
                pending.extend(modules[name]["imported_by"])
        if len(component) > 1 or start in modules[start]["local_imports"]:
            cycles.append(sorted(component))
    return sorted(cycles)


def inventory(root, roots=None):
    root = Path(root)
    defaults, configured = lake_roots(root)
    selected = sorted(set(defaults if roots is None else roots))
    paths, symlinks = source_paths(root)
    modules, errors, duplicates = {}, {}, {}
    identical_sources = defaultdict(list)
    for path in paths:
        relative = path.relative_to(root)
        data = path.read_bytes()
        source = data.decode("utf-8")
        name = module_name(relative.with_suffix("").parts)
        try:
            imports, import_only = parse_header(source)
            repeated = {dep: count for dep, count in Counter(imports).items() if count > 1}
            if repeated:
                duplicates[name] = repeated
            imports = list(dict.fromkeys(imports))
        except ValueError as error:
            errors[relative.as_posix()] = str(error)
            imports = []
            import_only = None
        modules[name] = {
            "path": relative.as_posix(), "category": classify(relative),
            "lines": len(source.splitlines()), "sha256": sha256(data).hexdigest(),
            "imports": imports, "imported_by": [], "import_only": import_only,
        }
        identical_sources[modules[name]["sha256"]].append(name)
    prefixes = {name.split(".", 1)[0] for name in modules.keys() | set(configured)}
    missing, unresolved = {}, {}
    external = set()
    for name, entry in modules.items():
        entry["local_imports"] = [dep for dep in entry["imports"] if dep in modules]
        for dep in entry["imports"]:
            if dep in modules:
                modules[dep]["imported_by"].append(name)
            elif dep.split(".", 1)[0] in prefixes:
                missing.setdefault(dep, []).append(name)
            elif dep.split(".", 1)[0] in EXTERNAL_PREFIXES:
                external.add(dep)
            else:
                unresolved.setdefault(dep, []).append(name)
    reached = closure(modules, selected)
    for name, entry in modules.items():
        entry["reachable"] = name in reached
        entry["imported_by"].sort()
    cycles = local_import_cycles(modules)
    source_manifest = sorted([entry["path"], entry["sha256"]] for entry in modules.values())
    categories = {}
    for category in sorted({entry["category"] for entry in modules.values()}):
        entries = [entry for entry in modules.values() if entry["category"] == category]
        categories[category] = {
            "files": len(entries), "lines": sum(entry["lines"] for entry in entries),
            "reachable": sum(entry["reachable"] for entry in entries),
        }
    report = {
        "schema": "unit-distance-source-inventory-v2",
        "scope": "Explicit source-header imports only; no elaboration, build, axiom audit, or external dependency verification.",
        "excluded_directory_names": sorted(EXCLUDED_DIRS),
        "skipped_symlinks": symlinks,
        "lake_default_roots": defaults, "lake_configured_roots": configured,
        "selected_roots": selected, "missing_roots": sorted(set(selected) - modules.keys()),
        "categories": categories, "modules": modules,
        "entry_points": sorted(name for name, entry in modules.items() if not entry["imported_by"]),
        "unreachable": sorted(modules.keys() - reached),
        "missing_local_imports": missing, "unresolved_imports": unresolved,
        "external_imports": sorted(external), "header_errors": errors,
        "local_import_cycles": cycles,
        "duplicate_imports": duplicates,
        "import_only_modules": sorted(name for name, entry in modules.items() if entry["import_only"]),
        "identical_source_groups": sorted(sorted(names) for names in identical_sources.values()
                                           if len(names) > 1),
        "source_manifest_sha256": sha256(json.dumps(source_manifest, separators=(",", ":"),
                                                   ensure_ascii=False).encode()).hexdigest(),
        "source_manifest_rule": "SHA-256 of UTF-8 compact JSON (ensure_ascii=False), no final newline; sorted [relative path, source SHA-256] pairs.",
    }
    selected_paths = {modules[name]["path"] for name in reached}
    report["selected_diagnostics"] = {
        "missing_roots": report["missing_roots"],
        "missing_local_imports": {dep: [name for name in users if name in reached]
                                  for dep, users in missing.items() if reached.intersection(users)},
        "unresolved_imports": {dep: [name for name in users if name in reached]
                               for dep, users in unresolved.items() if reached.intersection(users)},
        "header_errors": {path: message for path, message in errors.items() if path in selected_paths},
        "local_import_cycles": [cycle for cycle in cycles if reached.intersection(cycle)],
    }
    return report


def print_summary(report, list_unreachable=False, show=None):
    modules = report["modules"]
    print(f"Lean source inventory: {len(modules):,} files, "
          f"{sum(entry['lines'] for entry in modules.values()):,} lines")
    print("Category                Files       Lines   Reachable")
    for category, counts in report["categories"].items():
        print(f"{category:22} {counts['files']:6,} {counts['lines']:11,} {counts['reachable']:11,}")
    print("Selected roots: " + (", ".join(report["selected_roots"]) or "(none)"))
    print(f"Configured Lake roots: {len(report['lake_configured_roots'])}; "
          f"source entry points (no incoming local import): {len(report['entry_points'])}")
    library_unreachable = [name for name in report["unreachable"]
                           if modules[name]["path"] == "UnitDistance.lean"
                           or modules[name]["path"].startswith("UnitDistance/")]
    print(f"Outside selected closure: {len(report['unreachable'])} sources, "
          f"including {len(library_unreachable)} under UnitDistance")
    for key, label in (("missing_roots", "Missing selected roots"),
                       ("missing_local_imports", "Missing local import names"),
                       ("unresolved_imports", "Unrecognized import names"),
                       ("header_errors", "Header scan errors"),
                       ("local_import_cycles", "Local import cycles")):
        items = report[key]
        print(f"{label}: {len(items)}")
        for name in sorted(items):
            detail = f": {items[name]}" if isinstance(items, dict) else ""
            print(f"  {name}{detail}")
    print(f"External import names: {len(report['external_imports'])} (not checked)")
    print(f"Repeated-import sources: {len(report['duplicate_imports'])}; "
          f"import-only sources: {len(report['import_only_modules'])}; "
          f"identical-content groups: {len(report['identical_source_groups'])}")
    selected = report["selected_diagnostics"]
    print("Selected closure diagnostics: " + ", ".join(
        f"{len(selected[key])} {label}" for key, label in (
            ("missing_roots", "missing roots"), ("missing_local_imports", "missing local imports"),
            ("unresolved_imports", "unrecognized imports"), ("header_errors", "header errors"),
            ("local_import_cycles", "import cycles"))))
    print("Reachability is relative to these roots; outside the closure does not mean unused or disposable.")
    if list_unreachable:
        print("Sources outside selected closure:")
        for name in report["unreachable"]:
            print(f"  {name} [{modules[name]['category']}]")
    if show:
        entry = modules[show]
        print(f"\n{show}: {entry['path']} [{entry['category']}]")
        print(f"Local closure (including itself): {len(closure(modules, [show]))} sources")
        print("Imports:")
        for name in entry["imports"]:
            print(f"  {name}")
        print("Imported by:")
        for name in entry["imported_by"]:
            print(f"  {name}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--root", action="append", help="Selected dependency root; repeat for a union (default: Lake defaultTargets)")
    parser.add_argument("--json", action="store_true", help="Emit deterministic JSON with all module edges, hashes, roots, and importers")
    parser.add_argument("--list-unreachable", action="store_true", help="List every source outside the selected roots' closure")
    parser.add_argument("--show", metavar="MODULE", help="Show a source's direct imports, importers, and closure size")
    checks = parser.add_mutually_exclusive_group()
    checks.add_argument("--check", action="store_true", help="Fail on missing roots/imports, unknown namespaces, header errors, or import cycles in the SELECTED closure; report other sources without failing")
    checks.add_argument("--check-all", action="store_true", help="Apply import/header checks to the whole inventory, including scratch and historical verification sources")
    args = parser.parse_args(argv)
    try:
        report = inventory(args.source_root, args.root)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    if args.show and args.show not in report["modules"]:
        parser.error(f"module not found: {args.show}")
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False))
    else:
        print_summary(report, args.list_unreachable, args.show)
    diagnostics = report if args.check_all else report["selected_diagnostics"]
    return int((args.check or args.check_all) and any(diagnostics[key] for key in (
        "missing_roots", "missing_local_imports", "unresolved_imports", "header_errors", "local_import_cycles")))


if __name__ == "__main__":
    sys.exit(main())

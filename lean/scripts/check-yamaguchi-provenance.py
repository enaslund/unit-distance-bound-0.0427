#!/usr/bin/env python3
"""Verify vendoring and recover pinned upstream sources without a network checkout.

This checks provenance, not Lean correctness. Normal builds and axiom audits
are recorded separately. The only external command required is `patch`.
The later module-system layer, if present, is hash-checked and reversed before
checking the unchanged historical manifest and upstream recovery patches.
"""

from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

from module_port_provenance import ModulePort


ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "third-party/yamaguchi"
PREFIX = "UnitDistance.Upstream.Yamaguchi."
PIN = "3a455e1aa9140dbbe7b7d68f508392a69c86d0f4"
NOTICE = f"""/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
{PIN}, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

"""
MIGRATION_NOTICE = NOTICE.replace(
    "are recorded in third-party/yamaguchi/compatibility.patch.\n",
    "are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib\n"
    "4.35 Denumerable import relocation is recorded in\n"
    "third-party/yamaguchi/lean-v4.35-migration.patch.\n")
POWER_SERIES_MODULE = (
    "ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase."
    "PowerSeriesComposition")
POWER_SERIES_NOTICE = """/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.35 Mathlib now supplies the
formal log/exp composition proofs in Mathlib.RingTheory.PowerSeries.Log.
Original downstream declaration names and mathematical statements are retained.
-/

"""
POWER_SERIES_NOTICE_RECORD = (
    "The Lean 4.35 port replaces the local formal log/exp composition proofs "
    "with Mathlib.RingTheory.PowerSeries.Log results. The in-file notice "
    "records this proof replacement; the migration patch records the exact "
    "source change."
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def patched_paths(patch_text):
    """Return repository-relative source paths named by unified-diff headers."""
    paths = set()
    for line in patch_text.splitlines():
        if not line.startswith("+++ b/"):
            continue
        path = line[len("+++ b/"):]
        if path.startswith("Lean4/"):
            path = path[len("Lean4/"):]
        paths.add(path)
    return paths


def main():
    module_port = ModulePort(ROOT)
    manifest = json.loads((META / "manifest.json").read_text())
    require(manifest["upstream_commit"] == PIN, "Unexpected upstream pin")
    require(manifest["license"] == "Apache-2.0", "Unexpected license")
    entries = manifest["files"]
    notice_records = manifest.get("migration_notice_details", {})
    require(notice_records.get(POWER_SERIES_MODULE) == POWER_SERIES_NOTICE_RECORD,
            "PowerSeriesComposition migration notice is not documented in the manifest")
    require(manifest["local_modules"] == len(entries), "Module count mismatch")
    expected = {v["file"] for v in entries.values()}
    actual = {str(p.relative_to(ROOT)) for p in
              (ROOT / "UnitDistance/Upstream/Yamaguchi").rglob("*.lean")}
    require(actual == expected, "Vendored files and manifest differ")

    patch_text = (META / "compatibility.patch").read_text()
    # Historical patches used both upstream/Lean4/... and upstream/... paths.
    patch_text = re.sub(r"(?m)^(--- upstream|\+\+\+ compatible|\+\+\+ lean4\.32)/Lean4/",
                        r"\1/", patch_text)
    migration_patch = (META / "lean-v4.35-migration.patch").read_text()
    migration_paths = patched_paths(migration_patch)
    require(migration_paths, "Lean 4.35 migration patch contains no source paths")
    expected_paths = {
        name.replace(".", "/") + ".lean": name for name in entries
    }
    unknown_migrations = migration_paths - expected_paths.keys()
    require(not unknown_migrations,
            "Lean 4.35 migration patch names untracked source(s): "
            + ", ".join(sorted(unknown_migrations)))
    migrated_modules = {expected_paths[path] for path in migration_paths}
    changed = 0
    with tempfile.TemporaryDirectory(prefix="unit-distance-yamaguchi-") as tmp:
        destination = Path(tmp)
        for name, entry in entries.items():
            relative = name.replace(".", "/") + ".lean"
            require(entry["upstream_file"] == "Lean4/" + relative,
                    f"Upstream path mismatch: {name}")
            require(entry["module"] == PREFIX + name, f"Module mismatch: {name}")
            content = module_port.read(entry["file"])
            require(digest(content) == entry["sha256"], f"Vendored hash: {name}")
            text = content.decode()
            migrated = name in migrated_modules
            if name == POWER_SERIES_MODULE:
                # Before the new migration patch is recorded, the canonical
                # tree still carries its ordinary port notice. Once the
                # migration patch includes this file, preserve the specific
                # disclosure that Mathlib supplies the formal composition
                # proofs in place of the local proof bodies.
                notice = POWER_SERIES_NOTICE if migrated else NOTICE
            else:
                notice = MIGRATION_NOTICE if migrated else NOTICE
            require(text.startswith(notice), f"Modification notice: {name}")
            text = text[len(notice):]

            def imports(match):
                names = match[2].split()
                for imported in names:
                    if imported.startswith(PREFIX):
                        require(imported[len(PREFIX):] in entries,
                                f"Missing vendored dependency: {imported}")
                return (match[1] or "") + "import " + " ".join(
                    n[len(PREFIX):] if n.startswith(PREFIX) else n for n in names)

            text = re.sub(r"(?m)^(public )?import\s+([^\n]+)$", imports, text)
            path = destination / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            changed += entry["upstream_sha256"] != entry["compatible_sha256"]

        result = subprocess.run(
            ["patch", "--reverse", "--batch", "--fuzz=0", "-p1"],
            input=migration_patch, text=True, cwd=destination,
            capture_output=True)
        require(result.returncode == 0,
                "Mathlib 4.35 migration patch cannot be reversed over the "
                "reconstructed source tree:\n" + result.stdout + result.stderr)
        for name, entry in entries.items():
            path = destination / (name.replace(".", "/") + ".lean")
            require(digest(path.read_bytes()) == entry["compatible_sha256"],
                    f"Recovered pre-migration compatible hash: {name}")

        result = subprocess.run(
            ["patch", "--reverse", "--batch", "--fuzz=0", "-p1"],
            input=patch_text, text=True, cwd=destination, capture_output=True)
        require(result.returncode == 0,
                "Compatibility patch cannot be reversed:\n" + result.stdout + result.stderr)
        for name, entry in entries.items():
            path = destination / (name.replace(".", "/") + ".lean")
            require(digest(path.read_bytes()) == entry["upstream_sha256"],
                    f"Recovered upstream hash: {name}")

    print(json.dumps({"upstream_commit": PIN, "modules": len(entries),
                      "compatibility_modified": changed,
                      "hash_scope": "Historical vendored baseline after reversing any module-system layer",
                      "vendored_hashes": "passed", "import_relocation": "passed",
                      "v4_35_migration_reversed": "passed",
                      "v4_35_migration_modules": sorted(migrated_modules),
                      "compatible_hashes": "passed",
                      "reverse_patch_upstream_hashes": "passed",
                      "module_system_port": module_port.evidence()}, indent=2))


if __name__ == "__main__":
    main()

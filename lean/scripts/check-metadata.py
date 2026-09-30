#!/usr/bin/env python3
"""Check metadata against the public verifier pin inspected on 2026-09-27.

This does not build proofs, run the full verifier, or submit a package.
Historical checks require an explicit policy checkout and revision.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from source_inventory import parse_imports

ROOT = Path(__file__).resolve().parent.parent
CURRENT_PIN = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument(
    "--policy-tree",
    type=Path,
    default=ROOT / ".cache/upstream/PalomarSubmission-current-20260925-pinned",
)
parser.add_argument(
    "--revision",
    default=CURRENT_PIN,
    help="required PalomarSubmission commit (default: public pin inspected 2026-09-27; use an older SHA for historical replay)",
)
parser.add_argument(
    "--metadata",
    type=Path,
    action="append",
    help="metadata YAML to validate (repeatable; default: formalization-zeta.yaml if present, otherwise formalization.yaml)",
)
args = parser.parse_args()
policy = args.policy_tree.resolve()
actual = subprocess.check_output(["git", "-C", str(policy), "rev-parse", "HEAD"], text=True).strip()
if actual != args.revision:
    raise SystemExit(f"Wrong PalomarSubmission revision: {actual}; expected {args.revision}")
sys.path.insert(0, str(policy))
from scripts.submission_contract import load_formalization_metadata

metadata_paths = args.metadata or [
    Path("formalization-zeta.yaml") if (ROOT / "formalization-zeta.yaml").is_file()
    else Path("formalization.yaml")
]
metadata_results = []
for requested_path in metadata_paths:
    path = requested_path if requested_path.is_absolute() else ROOT / requested_path
    metadata = load_formalization_metadata(path.resolve(strict=True))
    metadata_results.append({
        "path": str(path.resolve()),
        "project": metadata["project"]["name"],
    })
challenges = {}
for challenge in sorted(ROOT.glob("Challenge*.lean")):
    name = challenge.name
    data = (ROOT / name).read_bytes()
    text = data.decode()
    imports = parse_imports(text)
    if not imports or not all(name == "Mathlib" or name.startswith("Mathlib.") for name in imports):
        raise SystemExit(f"Noncanonical direct challenge import in {name}: {imports}")
    if len(data) > 100 * 1024 or len(text.splitlines()) > 1000:
        raise SystemExit(f"Challenge size cap exceeded: {name}")
    challenges[name] = {"bytes": len(data), "lines": len(text.splitlines()), "imports": imports}
result = {
    "check": "Pinned Palomar metadata contract and direct Challenge size/import checks",
    "palomar_submission_commit": actual,
    "metadata": metadata_results,
    "challenges": challenges,
    "scope": "Local contract check only; not a Palomar pipeline run or registration",
}
print(json.dumps(result, indent=2))

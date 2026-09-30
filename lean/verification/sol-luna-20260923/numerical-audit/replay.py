#!/usr/bin/env python3
"""Sequential, guarded launcher for the isolated numerical audit receipts."""
from pathlib import Path
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3].parent
TASKS = [
    ("quadratic_h6", HERE / "numerics_afe_one_factor.py"),
    ("pure_quartic_afe", HERE / "numerics_afe_pure_quartic_direct.py"),
]
start = time.monotonic()
env = os.environ.copy()
flint_path = "/tmp/unit-distance-flint"
env["PYTHONPATH"] = flint_path + os.pathsep + env.get("PYTHONPATH", "")
for name, script in TASKS:
    begin = time.monotonic()
    result = subprocess.run([sys.executable, str(script)], cwd=ROOT, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / f"{name}.log").write_text(result.stdout)
    print(f"{name}: exit={result.returncode} seconds={time.monotonic()-begin:.3f}")
    if result.returncode:
        print(result.stdout[-5000:])
        raise SystemExit(result.returncode)
print(f"all PASS; total_seconds={time.monotonic()-start:.3f}")

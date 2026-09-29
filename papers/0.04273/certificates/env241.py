"""Path setup shared by the Q(sqrt 241) scripts.

Dependencies (the same pins as the 1.0418235 manuscript): mpmath 1.3.0 and
python-flint 0.9.0.  If they are not installed, set PYLIB to a directory
containing them (for example the unpacked PyPI wheels).

The certified profile, shell-window and degree-two AFE routines are imported
unchanged from the 1.0418235 supplementary archive.  The archive is verified
and unpacked once into CACHE (default: certificates/.cache) by the manuscript's
own unpacking routine, which checks every part and member hash.
"""
import importlib.util
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
MANUSCRIPT = REPO / "papers/0.0418235"
CACHE = Path(os.environ.get("CACHE241", HERE / ".cache"))
DESIGN = HERE.parent / "research/design-model"

if os.environ.get("PYLIB"):
    sys.path.insert(0, os.environ["PYLIB"])


def publication_archive():
    pub = CACHE / "publication"
    marker = CACHE / ".unpacked"
    if not marker.exists():
        CACHE.mkdir(parents=True, exist_ok=True)
        spec = importlib.util.spec_from_file_location("manuscript_reproduce", MANUSCRIPT / "certificates/reproduce.py")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        mod.unpack(CACHE)
        marker.write_text("verified by the manuscript unpack() member hashes\n")
    return pub


PUB = publication_archive()
for p in (PUB / "unit-distance-lower-bound/certificates", HERE, DESIGN):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def nonpositive_afe():
    return load("npafe", PUB / "five-prime-lower-bound/research/nonpositive-afe.py")


PAPER_WITNESS = MANUSCRIPT / "certificates/witness.json"

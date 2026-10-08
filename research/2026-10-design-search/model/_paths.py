"""Put the 1.04273 design model and certificate modules on sys.path."""
import os, sys
_here = os.path.dirname(os.path.abspath(__file__))
_root = os.path.abspath(os.path.join(_here, '..', '..', '..'))
for sub in ('papers/0.04273/research/design-model', 'papers/0.04273/certificates'):
    p = os.path.join(_root, sub)
    if p not in sys.path:
        sys.path.insert(0, p)

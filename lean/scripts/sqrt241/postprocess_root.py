#!/usr/bin/env python3
"""Generalize the generated copies of the √7 entireness chain to a radicand `d`.

Applied to the output of `copy_geometry.py` for the modules `HeckeSigned*`,
`HeckeQuadraticContinuation` and `ImaginaryQuadraticContinuation` in
`UnitDistance/Sqrt241/Geometry/`. The radicand-dependent leaves
(`QuadraticRoot*`, `ImaginaryRootUnramified`) are written by hand.

Usage: postprocess_root.py FILE...
"""
import re
import sys

RENAMES = [
    ('UnitDistance.Sqrt241.Geometry.QuadraticSevenNormCongruence',
     'UnitDistance.Sqrt241.Geometry.QuadraticRootNormCongruence'),
    ('UnitDistance.Sqrt241.Geometry.QuadraticSevenField',
     'UnitDistance.Sqrt241.Geometry.QuadraticRootField'),
    ('UnitDistance.Sqrt241.Geometry.QuadraticSevenIntegrality',
     'UnitDistance.Sqrt241.Geometry.QuadraticRootIntegrality'),
    ('UnitDistance.Sqrt241.Geometry.QuadraticSevenConjugation',
     'UnitDistance.Sqrt241.Geometry.QuadraticRootConjugation'),
    ('UnitDistance.Sqrt241.Geometry.ImaginarySevenUnramified',
     'UnitDistance.Sqrt241.Geometry.ImaginaryRootUnramified'),
    ('Sqrt241.QuadraticSeven.', 'Sqrt241.QuadraticRoot.'),
    ('Sqrt241.ImaginarySeven.', 'Sqrt241.ImaginaryRoot.'),
    ('_of_root_seven', '_of_root'),
    ('The actual root of seven discharges', 'An actual square root of `d` discharges'),
    ('of a number field containing sqrt(7), with', 'of a number field containing √d, with'),
]

HEADER_OLD = ('for the witness `UnitDistance.Sqrt241.Witness`:\n'
              'only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;')
HEADER_NEW = ('with the radicand `7` replaced by an\n'
              'admissible `d` (`QuadraticRoot.Admissible`, used with `d = 3`): only its\n'
              'radicand-dependent declarations, moved to `UnitDistance.Sqrt241`;')

VARIABLE = 'variable {d : ℕ} [Fact (UnitDistance.Sqrt241.QuadraticRoot.Admissible d)]'


def process(text):
    for a, b in RENAMES:
        text = text.replace(a, b)
    text = text.replace(HEADER_OLD, HEADER_NEW)
    text = re.sub(r'\(r : (\w+)\) \(hr : r\^2=7\)', r'(r : \1) (hr : r^2=(d : \1))', text)
    out = []
    lines = text.split('\n')
    for k, line in enumerate(lines):
        out.append(line)
        if (re.match(r'^namespace UnitDistance\.Sqrt241\.\S+\s*$', line) and
                (k + 1 >= len(lines) or lines[k + 1] != VARIABLE)):
            out.append(VARIABLE)
    return '\n'.join(out)


def main():
    for path in sys.argv[1:]:
        text = open(path).read()
        new = process(text)
        if new != text:
            open(path, 'w').write(new)
        left = [ln for ln in new.split('\n') if re.search(r'\b7\b|[Ss]even', ln)]
        for ln in left:
            print(f'{path}: {ln.strip()}')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Bind all manuscript inputs and certificate data, including nested TeX files.

An integrity check detects altered files and omitted proof dependencies.
It does not establish the mathematical correctness of their contents.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

if not __debug__:
    raise RuntimeError("Run without -O: assertions implement integrity checks")


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def proof_dependencies(root):
    root = root.resolve()
    pending = [root / 'main.tex']
    found = set()
    pattern = re.compile(r'\\(input|include|bibliography)\s*\{([^}]+)\}')
    while pending:
        path = pending.pop().resolve()
        if path in found:
            continue
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError(f'Missing or external manuscript input: {path}')
        found.add(path)
        if path.suffix != '.tex':
            continue
        text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
        for command, names in pattern.findall(text):
            for name in names.split(','):
                rel = Path(name.strip())
                if not rel.suffix:
                    rel = rel.with_suffix('.bib' if command == 'bibliography' else '.tex')
                pending.append(root / rel)
    return {str(p.relative_to(root)) for p in found}


def inputs(root):
    names = proof_dependencies(root)
    for pattern in ('*.tex', '*.bib', '*.pdf', '*.md', 'Makefile', 'requirements.txt',
                    'sections/*.tex', 'tools/*.py', 'certificates/*.py',
                    'certificates/*.json', 'certificates/*.tar.gz.part*', 'evidence/*.json',
                    'evidence/*.md'):
        names.update(str(p.relative_to(root)) for p in root.glob(pattern) if p.is_file())
    names.discard('certificates/manifest.json')
    return sorted(names)


def seal(root):
    names = inputs(root)
    record = {'exponent': '1.0418235',
              'scope': 'Source identity, complete manuscript dependency coverage, and bundled finite data; not a proof checker.',
              'proof_dependencies': sorted(proof_dependencies(root)),
              'sha256': {name: digest(root / name) for name in names}}
    (root / 'certificates/manifest.json').write_text(json.dumps(record, indent=2) + '\n')
    check(root)


def check(root):
    record = json.loads((root / 'certificates/manifest.json').read_text())
    assert record['exponent'] == '1.0418235'
    actual = proof_dependencies(root)
    assert actual == set(record['proof_dependencies']), 'Manuscript dependency closure changed'
    assert actual <= set(record['sha256']), 'Unbound mathematical proof input'
    archive = json.loads((root / 'certificates/data-manifest.json').read_text())
    parts = {'certificates/' + part['name'] for part in archive['archive_parts']}
    assert parts <= set(record['sha256']), 'Unbound supplementary archive part'
    for name, expected in record['sha256'].items():
        assert digest(root / name) == expected, f'Changed input: {name}'
    print(f"PASS identity of {len(record['sha256'])} package files; all {len(actual)} manuscript inputs covered")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seal', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    (seal if args.seal else check)(root)

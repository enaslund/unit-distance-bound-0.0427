#!/usr/bin/env python3
"""Portable certificate replay; extraction and computation occur in temporary storage.

Default: exact arithmetic checks and a fresh final geometric margin.
--analytic: additionally reevaluate every Hecke factor and the finite prime sum.
--moments: additionally rebuild and match all 64 newest sector moment files.
The full 10**12 prime sieve and earlier coefficient tables are retained data.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import time

if not __debug__:
    raise RuntimeError("Run without -O: assertions implement certificate checks")
sys.dont_write_bytecode = True
PAPER = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def unpack(destination):
    index = read(PAPER / 'certificates/data-manifest.json')
    archive = destination / 'data.tar.gz'
    digest = hashlib.sha256()
    size = 0
    assert index['archive_parts'], 'Missing archive parts'
    with archive.open('wb') as assembled:
        for number, part in enumerate(index['archive_parts']):
            assert part['name'] == f'data.tar.gz.part{number:02d}'
            data = (PAPER / 'certificates' / part['name']).read_bytes()
            assert len(data) == part['bytes']
            assert hashlib.sha256(data).hexdigest() == part['sha256']
            assembled.write(data)
            digest.update(data)
            size += len(data)
    assert size == index['archive_bytes']
    assert digest.hexdigest() == index['archive_sha256']
    with tarfile.open(archive, 'r:gz') as stream:
        members = stream.getmembers()
        assert len({m.name for m in members}) == len(members)
        assert {m.name for m in members} == set(index['files'])
        for member in members:
            path = (destination / member.name).resolve()
            assert member.isfile() and path.is_relative_to(destination.resolve())
            path.parent.mkdir(parents=True, exist_ok=True)
            data = stream.extractfile(member).read()
            assert hashlib.sha256(data).hexdigest() == index['files'][member.name]
            path.write_bytes(data)
    return destination / 'publication'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check source identity and complete TeX dependency coverage only')
    parser.add_argument('--analytic', action='store_true')
    parser.add_argument('--moments', action='store_true')
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output', type=Path, help='optional JSON receipt path')
    args = parser.parse_args()
    assert 1 <= args.workers <= 16
    checker = load('consolidated_manifest', PAPER / 'tools/manifest.py')
    checker.check(PAPER)
    if args.check:
        return
    started = time.monotonic()
    tower_record = load('independent_manuscript_tower', PAPER / 'certificates/check_tower.py').verify()
    field_record = load('independent_manuscript_field', PAPER / 'certificates/check_field.py').verify()
    with tempfile.TemporaryDirectory(prefix='unit-distance-1.0418235-') as name:
        pub = unpack(Path(name))
        table_record = load('manuscript_analytic_table', PAPER / 'certificates/check_analytic_table.py').verify(pub)
        h7 = pub / 'seven-dimensional-dyadic-lower-bound/certificates'
        retuned = pub / 'retuned-profile-lower-bound/certificates'
        analytic_record = None
        if args.analytic or args.moments:
            command = [sys.executable, '-B', str(h7 / 'reproduce.py'), '--workers', str(args.workers)]
            if args.moments:
                command.append('--full')
            subprocess.run(command, check=True)
            analytic_record = read(h7 / 'replay.json')
            assert analytic_record['status'].startswith('PASS')
        subprocess.run([sys.executable, '-B', str(retuned / 'reproduce.py')], check=True)
        geometry = read(retuned / 'geometry.json')
        assert geometry['status'].startswith('PASS')
        record = {
            'status': 'PASS consolidated certificate replay',
            'exponent': '1.0418235',
            'independent_tower_check': tower_record,
            'independent_retained_field_check': field_record,
            'printed_analytic_table_check': table_record,
            'geometry': geometry,
            'all_analytic_factors_reevaluated': bool(analytic_record),
            'newest_64_moment_files_regenerated': args.moments,
            'analytic_replay': analytic_record,
            'complete_prime_sieve_regenerated': False,
            'all_earlier_moment_and_actual_field_data_regenerated': False,
            'seconds': time.monotonic() - started,
        }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2) + '\n')
    print('PASS 1.0418235; fresh margin:', geometry['margin_after_concentration'])


if __name__ == '__main__':
    main()

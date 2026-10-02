#!/usr/bin/env python3
"""Check the source-only snapshot against its shipped SHA256 inventory."""
from pathlib import Path, PurePosixPath
import hashlib
import re

root = Path(__file__).resolve().parents[1]
manifest = root / 'checks/source-files.sha256'
expected = {}
for line in manifest.read_text().splitlines():
    match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
    if not match:
        raise SystemExit('Invalid checksum inventory line')
    digest, name = match.groups()
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or name in expected:
        raise SystemExit('Invalid or duplicate inventory path: ' + name)
    expected[name] = digest
for name, digest in expected.items():
    path = root / name
    if not path.is_file() or path.is_symlink():
        raise SystemExit('Missing or linked source file: ' + name)
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit('Changed source file: ' + name)
print(f'PASS: {len(expected)} inventoried source/verification files match SHA256.')
print('The inventory excludes itself. Use the separately supplied ZIP checksum to anchor the whole archive.')

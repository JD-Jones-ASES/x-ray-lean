#!/usr/bin/env python3
"""Fail until all advertised statements are present in the solution."""
from pathlib import Path
import json
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
subprocess.run(['python3', 'scripts/check_source.py'], cwd=root, check=True)
with tempfile.TemporaryDirectory(prefix='xray-release-') as tmp:
    probe = Path(tmp) / 'ReleaseCheck.lean'
    probe.write_text('import Solution\n' + '\n'.join(
        '#check @' + name for name in config['theorem_names']) + '\n')
    subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=root, check=True)
print('All advertised declarations exist. Comparator and independent kernel replay are still required.')

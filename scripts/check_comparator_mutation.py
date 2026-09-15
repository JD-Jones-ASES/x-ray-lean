#!/usr/bin/env python3
"""Confirm Comparator rejects a changed mathematical definition; restore afterwards."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('comparator', type=Path)
    args = parser.parse_args()
    binary = args.comparator.resolve(strict=True)
    challenge = ROOT / 'Challenge.lean'
    original = challenge.read_bytes()
    text = original.decode()
    old = '''  StrictMono L ∧ (∀ i, 1 ≤ L i ∧ L i ≤ 2 * (n : ℤ) - 1) ∧
    (∀ k ≤ n, 0 ≤ slack L k) ∧ slack L n = 0'''
    if text.count(old) != 1:
        raise RuntimeError('Expected one explicit admissibility definition')
    config = json.loads((ROOT / 'comparator.json').read_text())
    if config.get('definition_names'):
        raise RuntimeError('This control requires comparison without definition holes')
    config['enable_nanoda'] = False
    try:
        challenge.write_text(text.replace(old, '  True'))
        with tempfile.TemporaryDirectory(prefix='xray-comparator-control-') as tmp:
            cfg = Path(tmp) / 'comparator.json'
            cfg.write_text(json.dumps(config))
            result = subprocess.run(['lake', 'env', str(binary), str(cfg)], cwd=ROOT,
                                    capture_output=True, text=True)
            output = result.stdout + result.stderr
            if result.returncode == 0 or "Const does not match" not in output:
                raise RuntimeError(f'Comparator did not reject the definition change as intended:\n{output}')
            print('\n'.join(line for line in output.splitlines() if 'does not match' in line))
    finally:
        challenge.write_bytes(original)
        subprocess.run(['lake', 'build', 'Challenge'], cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
    print('Comparator rejected the changed admissibility definition; original Challenge restored.')


if __name__ == '__main__':
    main()

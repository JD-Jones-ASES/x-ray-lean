#!/usr/bin/env python3
"""Exercise the source guard and all-declaration axiom audit, then restore files."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def rejected(command, expected):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode == 0 or expected not in output:
        raise RuntimeError(f'Negative control did not reject as intended:\n{output}')


def main():
    scratch = ROOT / 'XRay' / 'MutationControl.lean'
    if scratch.exists():
        raise RuntimeError(f'Refusing to overwrite {scratch}')
    try:
        scratch.write_text('import Mathlib\ntheorem mutation_control : True := by sorry\n')
        rejected(['python3', 'scripts/check_source.py'], 'prohibited token sorry')
        scratch.write_text('import Mathlib\nexample : True := by native_decide\n')
        rejected(['python3', 'scripts/check_source.py'], 'prohibited token native_decide')
    finally:
        scratch.unlink(missing_ok=True)

    audit = ROOT / 'Test' / 'Axioms.lean'
    original = audit.read_bytes()
    try:
        text = original.decode().replace('open Lean in',
            'axiom XRay.mutation_control : False\n\nopen Lean in', 1)
        audit.write_text(text)
        rejected(['lake', 'env', 'lean', 'Test/Axioms.lean'],
                 'Unexpected axiom XRay.mutation_control')
    finally:
        audit.write_bytes(original)
    subprocess.run(['python3', 'scripts/check_source.py'], cwd=ROOT, check=True)
    print('Three negative controls rejected correctly; original sources restored.')


if __name__ == '__main__':
    main()

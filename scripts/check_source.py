#!/usr/bin/env python3
"""Reject unfinished proofs and kernel bypasses in the solution sources."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
BANNED = re.compile(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b|Lean\.ofReduceBool|debug\.(?:skipKernelTC|byAsSorry)')
BYPASS = re.compile(r'debug\.(?:skipKernelTC|byAsSorry)|\bnative_decide\b')


def code_only(text):
    """Blank strings and nested comments, retaining line positions."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            ch = text[i]
            if ch != '\n': out[i] = ' '
            if ch == '\\' and i + 1 < len(text):
                i += 1
                if text[i] != '\n': out[i] = ' '
            elif ch == '"': string = False
            i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n': out[i] = ' '; i += 1
        elif text[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('unclosed comment or string')
    return ''.join(out)


def main():
    files = sorted((ROOT / 'XRay').rglob('*.lean')) + sorted((ROOT / 'Test').rglob('*.lean'))
    files += [ROOT / name for name in ['XRay.lean', 'Solution.lean', 'Test.lean']]
    failed = False
    for path in files + [ROOT / 'Challenge.lean']:
        if not path.is_file():
            print(f'Missing required source: {path.relative_to(ROOT)}'); failed = True; continue
        code = code_only(path.read_text())
        pattern = BYPASS if path.name == 'Challenge.lean' else BANNED
        for match in pattern.finditer(code):
            line = code.count('\n', 0, match.start()) + 1
            print(f'{path.relative_to(ROOT)}:{line}: prohibited token {match.group()}')
            failed = True
    if failed: return 1
    print(f'Checked {len(files)} solution and audit files; no prohibited proof tokens.')
    return 0

if __name__ == '__main__':
    sys.exit(main())

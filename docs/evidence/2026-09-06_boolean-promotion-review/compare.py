#!/usr/bin/env python3
"""Mechanical comparison for these inspected, non-nested-comment snapshots."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent


def declarations(path):
    source = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    starts = list(re.finditer(r'^theorem ([^\s{(:]+)', source, re.M))
    result = {}
    for i, match in enumerate(starts):
        stop = starts[i + 1].start() if i + 1 < len(starts) else len(source)
        body = re.split(r'^end ', source[match.start():stop], 1, flags=re.M)[0].strip()
        assert match[1] not in result
        result[match[1]] = body
    return result


current = declarations(root / 'BooleanProgram.lean')
pool = declarations(root / 'BooleanPool.lean')
assert not current.keys() & pool.keys()
current.update(pool)
assert declarations(root / 'FrozenProgram.lean') == current
tests = declarations(root / 'BooleanProgramTests.lean')
assert declarations(root / 'FrozenTests.body') == tests
print(f'Exact theorem declaration/body equality (comments and module imports omitted): '
      f'{len(current)}/{len(current)} program theorems, {len(tests)}/{len(tests)} supplied test theorems.')

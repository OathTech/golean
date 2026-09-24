#!/usr/bin/env python3
"""[AGENT] Reproduce the customer's GENERATED f2 proof variants WITHOUT running
anything in their (read-only) repo.

Their generator is `tools/check_f2_proofs.py`, function
`check_native_proof_variants` (lines ~125-165 at their commit): a table of
(label, old, new, reject_module) applied as `source.replace(old, new, 1)` to
`examples/fixtures/f2/main.go`, written as `subject.go` into a fresh directory
that is then lowered with `--dir`.

This script parses that table out of their source with `ast.literal_eval` (no
execution of their code), applies the same substitution under their own guard
(their line 159), and writes the units into our scratch. It therefore
reproduces the generator's OUTPUT, not a re-implementation of its intent.

Usage (from the repo root):
  python3 docs/evidence/2026-09-24_customer-fixture-inventory/gen-f2-variants.py \
      <customer-repo-root> .tmp/inventory/src
"""
import ast
import pathlib
import sys

CUST = pathlib.Path(sys.argv[1])
OUT = pathlib.Path(sys.argv[2])
SRC = CUST / 'tools/check_f2_proofs.py'

tree = ast.parse(SRC.read_text())
fn = next(n for n in ast.walk(tree)
          if isinstance(n, ast.FunctionDef) and n.name == 'check_native_proof_variants')
tbl = None
for stmt in fn.body:
    if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
            and getattr(stmt.targets[0], 'id', None) == 'variants'):
        tbl = ast.literal_eval(stmt.value)
if tbl is None:
    raise SystemExit('variants table not found in ' + str(SRC))

source = (CUST / 'examples/fixtures/f2/main.go').read_text()
for label, old, new, _reject in tbl:
    # their own guard (check_f2_proofs.py:159), verbatim in effect
    if old not in source or (label != 'wrong-capture-target' and source.count(old) != 1):
        raise SystemExit('F2 variant target missing/ambiguous: ' + label)
    d = OUT / ('f2-proof-' + label)
    d.mkdir(parents=True, exist_ok=True)
    (d / 'subject.go').write_text(source.replace(old, new, 1))
    print('generated', d.name)

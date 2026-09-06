# Independent recovery entry facade promotion review

[AGENT] `typed-preflight`, 2026-09-06 UTC. **Bounded PASS** for the parent
promotion at `4158368f` with entry `63769964` pending integration, bound to
`source-hashes.json`. This reviews the facade, public audit and gate wiring;
the entry implementation has the separate bounded review `997d74ed`.

`source.tar.gz` retains the five promotion code inputs, claim ledger and
all 13 previously reviewed entry inputs. `compare.py` verifies the entry
source/test/gate inputs against their earlier frozen manifest. The only
permitted byte change among them is removal of one final LF from
`tools/recovery-setup-audit.py`; its Python AST is identical. No theorem,
definition, judgment or executable helper was changed by this promotion.

The facade imports `RecoveryCallEntry` and exposes its transitive reusable
contracts. Its prose and the updated entry ledger accurately limit these
to actual setup/call/defer entry, typed initialized storage, exact readout,
world extension, structural bounds and unchanged choices. They do not claim
full recovery control preservation, successful rendering, Iris ownership,
or a stable interface. The ledger explicitly separates completed entry
validation from the still-required public promotion gates.

The public audit now requires 84 distinct theorem exports, adding 12 entry
contracts. The Lean and Python required-module inventories agree; every new
storage/entry module and test module is in the shell's fresh elaboration
list. The four existing core/admission prerequisites are built by Lake
instead of separately elaborated by that shell list. Origin selection
continues to sweep all imported GoLean/Tests and local declarations,
including unused/private/generated/trailing declarations, with only the
classical trio allowed. The constructive renderer restriction remains.
Neither facade promotion nor its dependency graph imports Iris or the
frontend/CLI.

All 15 previous compiled poison controls are retained unchanged, with four
additional poisons in the storage helper, setup-well-formedness helper,
call-entry helper and setup test. Each mutated source must compile before
the separate post-import audit must return the named forbidden-axiom
failure. This is not a source-text-only negative test.

Fresh independent checks:

```sh
python3 docs/evidence/2026-09-06_recovery-entry-promotion-review/compare.py
# From the parent's worktree, using its frozen compiled dependencies:
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean ../typed-preflight/docs/evidence/2026-09-06_recovery-entry-promotion-review/Probes.lean
```

`comparison-2.log` and `probes.log` both record exit 0. The facade-only
Lean probe resolves all 12 promoted theorems and reports the actual axiom
dependencies of generic setup, call entry and initialized readout. The
earlier comparison log records an overly strict reviewer assumption that
only Machine was omitted from the shell's explicit elaboration list; the
three existing admission prerequisites are likewise built by Lake. The
corrected check distinguishes this from omission of a new public module.

The parent's ordinary CI was still live when this bounded source verdict
was sealed. Its eventual terminal status and the fresh 19-poison public
gate, affected native and spike gates remain integration obligations.
This report does not assert them passed and does not repeat the full corpus.

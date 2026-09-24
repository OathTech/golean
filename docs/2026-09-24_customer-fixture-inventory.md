# The logic team's fixtures under `main`'s frontend — the `unseq` inventory (2026-09-24)

[AGENT] records worker, lane `records/customer-fixture-inventory-0924`. Charter row 0 of
`docs/2026-09-23_batched-window-charter.md` («the fixture INVENTORY (F3 procedure)»), run to the
procedure the Codex review prescribed (`docs/2026-09-23_batched-window-charter-review.md` F3: the
pinned production frontend with an owned scratch `--out` per unit, recursive JSON statement counts,
a failed export never reported as zero graphs, `lower-diagnose` for failures only). Authority:
[USER] Mike 2026-09-24 («I'm happy to go with your rec»), relayed. Records only — no runtime code,
no baseline, no gate touched. Evidence:
`docs/evidence/2026-09-24_customer-fixture-inventory/` (counts TSV, the walker, the generator
reproduction, per-unit stderr, wire digests, the positive control); wires stay in scratch.

## 1. What was under test

The proposal states as an inference, not a measurement
(`docs/2026-09-23_proposal-to-logic-team.md` §1 item 3): «**[inf]** None of your fourteen fixtures
(`L:examples/fixtures/*/main.go`) enters a graph … We have NOT verified this by lowering your
fixtures with `main`'s frontend». The logic team replied (`docs/2026-09-23_response-from-logic-team.md`
§1): «All fourteen native fixture directories should be re-lowered. Your claim that none triggers
`unseq` remains a hypothesis until that check, including our generated positive variants.»

## 2. Pins

| Pin | Value |
|---|---|
| Customer source | `golean-logic` @ `b2c37c1492a16de317de40b2c487f478c8b9c6a1` (2026-09-22), clean, read-only to this lane |
| Our tree | `main` @ `3fb4a0d18debdc3ffd8e364e723326f475a7369f`; `HEAD:tools/nativefrontend` = `9fe2042c4c9ac806e6bab470e1c6a4a472d19985` |
| Frontend binary | sha256 `e61605f5fe2ed7f2a2fb3eb0db9cfd436a234f899915d5ab902f6347aa7c33cf` (`GO111MODULE=off go build -o … ./tools/nativefrontend`, the driver scripts' invocation) |
| Go toolchain | `go1.26.5 linux/amd64` = the pin in `baselines/go-oracle-pin` |

The customer builds against `golean` @ `61958f2e` (`provenance/pins.json`); this inventory runs OUR
`main` deliberately — that is the frontend the re-pin offer would ship. [AGENT]

## 3. The units

Fourteen fixture directories, as their manifest and check scripts name them, plus the **generated
positive variants**: the generator is `tools/check_f2_proofs.py` `check_native_proof_variants`
(their lines 125–165), a table of textual substitutions on
`examples/fixtures/f2/main.go`, written as `subject.go` into a fresh directory that is then lowered —
five `positive-*` and three `wrong-*`. Since the table is data, this lane REPRODUCED the eight units
by parsing it with `ast.literal_eval` and applying the same `replace(old, new, 1)` under their own
guard, copying the source out; nothing was run in their repo ([AGENT] — `gen-f2-variants.py` in the
evidence dir). Their other "variants" (`e1-equivalent`, `e1-local`, `e1-wrong`, `f1-alternative`,
`f1-s-*`) are checked-in fixture directories, already among the fourteen. Their `*-native` scratch
directories (fixture `main.go` + `tools/{e1,f1,f2}-native-main.go`) are observation harnesses run
with `go run .`, never lowered — their only `nativefrontend` call sites are `tools/check.py:153`,
`check_e1.py:62,99`, `check_f2.py:60`, `check_f2_proofs.py:164`, so nothing lowered is uncovered.

## 4. Results

Statement nodes are counted by a recursive walk of the whole retained wire — every JSON object with a
string `"stmt"` key (`stmtAllowedKeys`, `GoLean/NativeToIR.lean` ~line 170) — not by a grep. Graph
nodes are `"stmt":"unseq"`; body kinds are its `occs[].kind` (`eval`/`invoke`/`target`/`load`/
`guard`/`recv`/`allocate`/`wide`, `unseqOccAllowedKeys`); the legacy probe is `"stmt":"unseq-probe"`.
The last column is the `--unseq-census` sweep row count — ADDITIONAL evidence, documented as a
MAIN-UNIT census (its help text), not a substitute for the wire.

| Unit | Export | Stmts | `unseq` | Body kinds | `unseq-probe` | Sweep rows (all `legacy`) |
|---|---|---|---|---|---|---|
| `callchain` | ok (exit 0, stderr empty) | 10 | 0 | none | 0 | 6 |
| `e1` | ok (exit 0, stderr empty) | 49 | 0 | none | 0 | 37 |
| `e1-equivalent` | ok (exit 0, stderr empty) | 49 | 0 | none | 0 | 37 |
| `e1-local` | ok (exit 0, stderr empty) | 62 | 0 | none | 0 | 48 |
| `e1-wrong` | ok (exit 0, stderr empty) | 49 | 0 | none | 0 | 37 |
| `error-string` | ok (exit 0, stderr empty) | 10 | 0 | none | 0 | 3 |
| `f1` | ok (exit 0, stderr empty) | 45 | 0 | none | 0 | 36 |
| `f1-alternative` | ok (exit 0, stderr empty) | 45 | 0 | none | 0 | 36 |
| `f1-s-local` | ok (exit 0, stderr empty) | 49 | 0 | none | 0 | 40 |
| `f1-s-results` | ok (exit 0, stderr empty) | 45 | 0 | none | 0 | 36 |
| `f1-s-wrong-target` | ok (exit 0, stderr empty) | 45 | 0 | none | 0 | 36 |
| `f2` | ok (exit 0, stderr empty) | 57 | 0 | none | 0 | 42 |
| `recovery` | ok (exit 0, stderr empty) | 16 | 0 | none | 0 | 9 |
| `shared` | ok (exit 0, stderr empty) | 69 | 0 | none | 0 | 37 |
| `f2-proof-positive-set` (gen.) | ok (exit 0, stderr empty) | 60 | 0 | none | 0 | 45 |
| `f2-proof-positive-closure` (gen.) | ok (exit 0, stderr empty) | 58 | 0 | none | 0 | 43 |
| `f2-proof-positive-declare-after-defer` (gen.) | ok (exit 0, stderr empty) | 59 | 0 | none | 0 | 44 |
| `f2-proof-positive-declare-before-defer` (gen.) | ok (exit 0, stderr empty) | 59 | 0 | none | 0 | 44 |
| `f2-proof-positive-block-fallthrough` (gen.) | ok (exit 0, stderr empty) | 59 | 0 | none | 0 | 44 |
| `f2-proof-wrong-helper-value` (gen.) | ok (exit 0, stderr empty) | 57 | 0 | none | 0 | 42 |
| `f2-proof-wrong-shared-order` (gen.) | ok (exit 0, stderr empty) | 57 | 0 | none | 0 | 42 |
| `f2-proof-wrong-capture-target` (gen.) | ok (exit 0, stderr empty) | 57 | 0 | none | 0 | 42 |

22 / 22 exported. Statement totals 1066; `unseq` 0; graph-body occurrences 0 in every kind;
`unseq-probe` 0. All 786 sweep rows across the 22 units read `legacy`; the census's only other value,
`unseq`, appears in none. Full statement histograms are in `counts.tsv`: the units are
`assign`/`block`/`return`/`expr`/`defer`/`if`/`var`, with `panic`, `new`, `make-map` and `map-assign`
in `recovery`/`shared`/`error-string`/`e1*`. No export failed, so **no row is a zero-by-refusal**, and
`scripts/lower-diagnose` was not needed (F3 confines it to explaining failures; it deletes its probe
wire and cannot certify absence).

**The instrument's positive control.** An all-zero table is what a broken counter also prints. The
same binary and walker over two of our own emitting packages give `len-vs-call-order` = 4 `unseq` /
15 `unseq-probe` and `e13-sibling-panic-order` = 50 / 11 — the numbers
`docs/evidence/2026-09-22_unseq-stage-e5/probes-e5d.txt` records for them — with body kinds populated
(for `e13-sibling-panic-order`: `eval` 155, `invoke` 52, `target` 16, `load` 8, `recv` 5, `allocate` 11,
`wide` 4), and the census's `unseq` row counts (4, 50) agree with the wire — both instruments report
non-zero when a graph exists.

## 5. Verdict

**Confirmed as measured, at the pins of §2, for the 22 units of §3**: no unit of the logic team's
fourteen fixture directories, and none of the eight variants their `f2` generator produces, emits a
`"stmt":"unseq"` graph node or any legacy `"stmt":"unseq-probe"` statement under `main`'s frontend.
The proposal's **[inf]** (§1 item 3) becomes a measurement, and their §1 condition («a hypothesis
until that check, including our generated positive variants») is met for the lowering step. [AGENT]

## 6. What this does NOT establish

1. **Nothing about E6.** These counts are the frontend at `3fb4a0d1`; E6a–E6e widen the `unseq`
   grammar (charter §1), so units that lower legacy today may lower to graphs afterwards — the
   measurement must be REPEATED at the window's close, before the re-pin offer.
2. **Nothing about their build or their proofs.** No Lean was built, nothing in `golean-logic` was
   run; whether their artifacts still elaborate against `main` is the charter's row-7 question, and
   their acceptance remains `scripts/check` plus their own theorems and consumers.
3. **Not a differential result.** No program was executed, no oracle consulted, no observation
   compared: a lowering-shape census only, saying nothing about these units' fidelity.
4. **Not a statement about their source fragment.** Per their §1, «general panic/recovery remains
   future work in the live source calculus» — `recovery` and `shared` lower here, which does not
   mean their admission accepts them.
5. **Only the units lowered** (§3): if their generator table changes, re-run the reproduction.

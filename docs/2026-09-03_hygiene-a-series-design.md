# The A-series — design note and preservation arguments (2026-09-04)

Status: IN PROGRESS on branch `hygiene-a-series` (design-hygiene arc step
(ii); plan `docs/2026-09-03_design-hygiene-arc.md`; source proposals
`docs/2026-09-03_grumpy-professor-review.md` §3(a) A1–A10). Provenance:
[AGENT] execution inside the [USER]-ratified arc (Mike, 2026-09-03,
relayed by the [AGENT] coordinator, not firsthand: «Great, let's do it as
you propose … our aim is to get the *nicest* faithful go semantics»);
every design choice below is [AGENT] unless marked. Evidence dir:
`docs/evidence/2026-09-03_hygiene-a-series/`. Template: the B1 note
(`docs/2026-09-03_hygiene-b1-stamps-design.md`).

Conventions (review §3): "preserving" = for every program, stream and
fuel the same `Except GoError Result` (constructor, message, readout),
and the choice tape consumed at the same sites with the same bounds in
the same order. Each item below is ONE commit, gated by the full
`scripts/capped scripts/ci --diff` at ZERO baseline drift and by the
whole-corpus labeled-consumption trace (`scripts/choice-trace-corpus`,
6 streams × every executable row) at ZERO consumption delta against the
pre-series snapshot taken at `1b8401c0` (main, both prerequisite lanes
landed). The two prerequisite lanes (`bug087-paniktext` → ChoiceSite
`nilValueMethodText`; `q-trylock` → ChoiceSite `tryLock`) were waited for
per the coordinator's brief; the branch forks from `1b8401c0`.

## Pre-series findings (recorded before the first edit)

- **A4 wire impact: NONE.** The wire already carries
  `{"expr":"globaladdr","gid":N}` (tools/nativefrontend/emit.go
  `globalAddr`); only the DECODER (`GoLean/NativeToIR.lean` `"globaladdr"`
  arm) turns it into a core node. The twin-wire pin
  (`baselines/pins/twin-chdriver.wire.json`, `scripts/check-frontend-pins`)
  pins the frontend's EMITTED bytes, which A4 does not touch. So A4 moves
  no pin and needs no [USER] call; the brief's STOP condition was not
  met.
- **The baseline carries no refusal class or message**
  (`baselines/native-full.tsv` is `result id stage` with stage ∈
  {frontend-export, lean-observation, differential, confluent}), so A9's
  re-tagging of refusal classes is drift-free by construction as long as
  no row's PASS/FAIL result or stage moves; the differential is still run
  as the check.
- `GoValue.unit` is NOT dead (review A8 lists it): `atomicCompute`'s
  `.store` arm returns it as the "no result" value (Machine.lean). A8
  treats it accordingly (see §A8).
- `Expr.length/capacity`'s `typ` constant-folding (A8) is a FRONTEND
  change (emit.go) — outside this lane's rules (no frontend/wire change
  unless the item is about it); SKIPPED, recorded at §A8.

## A1 — the stop grammar as types: `Refusal` / `Terminal` / `GoError`

**What changed** (Value.lean). `GoError` is now
`refusal (r : Refusal) | terminal (t : Terminal) | fuelOut` with
`Refusal := unsupported | stuck | internal` and
`Terminal := panic | fatal | deadlock | raceDetected`. `GoError.status`
and `.message` are per-class projections (`Refusal.status/message`,
`Terminal.status/message`) composed at the top; the status TABLE is
byte-identical to the old flat one (`internal` → `"error"`, `fuelOut` →
`"fuel-out"`, …), so the CLI observation JSON does not move. The review's
`Budget := fuelOut` singleton is kept as the bare constructor
`GoError.fuelOut` (a one-constructor wrapper type would add a level to
every fuel proof for no classification gain; the budget class IS the
constructor). [AGENT]

**The compatibility view.** The seven flat names the machine has always
used (`.panic m`, `.stuck m`, `.unsupported f`, `.internal m`, `.fatal m`,
`.deadlock`, `.raceDetected`) remain valid in BOTH term and pattern
position: they are `@[match_pattern] abbrev`s over the nested type
(`GoError.panic m := .terminal (.panic m)` etc.). So NO `throw` site and
NO `| .error (.panic msg) =>` arm moved (the review estimated "hundreds"
of mechanical edits — this makes them zero; the B2 wave that retires the
panic carrier is where callers move). `simp` sees the view exactly as it
saw constructors through a generated family of 4 injectivity + 42
pairwise-disjointness `@[simp]` lemmas (`GoError.panic_inj`,
`GoError.stuck_ne_panic`, …), and a `cases_stop e` tactic macro
(`rcases e with (_|_|_) | (_|_|_|_) | _`) reproduces the old eight-way
`cases e` shape where a proof enumerated the constructors; `case panic
msg =>` selects by tag suffix as before.

**Why nicer.** "Which stops are Go behaviours" is a type: `Terminal` is
what the differential compares, `Refusal` is what the machine declines,
`fuelOut` is the model's budget. The refusal RULE (A9) has a home
(`Refusal`'s constructor docstrings). Downstream adequacy statements can
quantify `Terminal` instead of "the subset of `GoError` I mean".

**Preservation.** A bijection on constructors (`flat ↔ nested`), the
status/message tables unchanged; every machine definition is unchanged
text whose elaboration goes through the view abbrevs. Exact.

**Proof deltas** (arm for arm): `exceptCong.panic_left` (MachineSound)
splits the nested type explicitly; two `cases e <;> simp_all` sites in
`applySelect`'s wf/normalization proofs (StateWf) split the terminal
class; five `cases e <;> …` sites in MultiSound, one in MultiWfSound,
two in EnumDedupSound go through `cases_stop`. No lemma deleted, none
weakened; two `simp` calls in MachineSound (`applySyncOp_panic_any_ch`,
the empty-picks select arm) gained the view unfoldings.

**Gate.** `scripts/capped scripts/ci --diff` on the A1 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394
(`docs/evidence/2026-09-03_hygiene-a-series/transcripts/gate-a1.txt`; run
on the uncommitted A1 sources — the tree that became the A1 commit, no
edit between run and commit; the series-final clean-tip gate is in the
records commit). Choice-trace delta vs the pre-series snapshot: see the
evidence README (A1 row).

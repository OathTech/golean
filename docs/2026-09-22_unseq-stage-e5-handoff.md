# Stage E5 of the evaluation-order model v2.1 — lane handoff (`core/unseq-stage-e5-0922`)

[AGENT] worker, 2026-09-22. Worktree `.claude/worktrees/unseq-stage-e5`, branch `core/unseq-stage-e5-0922`,
based on main `d76721bd` (train r46's 5a records; main's records-only close `dc5de785` landed after the
branch — rebased at the lane's end). Brief: the Stage E handoff §3 (`docs/2026-09-21_unseq-stage-e-handoff.md`)
under the seven rulings of 2026-09-22 ([USER] Mike «Agree on the judgements, go ahead», relayed —
`docs/2026-08-31_qrow-rulings.md`); the family plan and every [AGENT] choice:
`docs/2026-09-22_unseq-stage-e5-design.md`; evidence `docs/evidence/2026-09-22_unseq-stage-e5/`. NOT merged,
NOT pushed. Every runtime commit below is GATED (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` under
the box-wide lock; when the wire schema, the decoder or the core changed the gate is red on EXACTLY the two
5a-class items — `certificate provenance` STALE + the `imported-goose/channel/google-search` drift line — and
nothing else; the train installs the candidate at step 5a, this lane does not).

## 1. State at park

| commit | family | gate | rows | census (admitted / probes corpus+twin) | trace |
|---|---|---|---|---|---|
| (E5d, this tree) | **E5d** the ADDRESS of a variable as an operand — an address formation (no read, no failure), NO occurrence; an ALLOWED LIST of value positions (argument, receiver, payload, plain stored value, return, tuple beside no planned target); the decoder gains ONE payload arm (`ref`/`globaladdr`; `ref $cell` refused — F2); no core change | `ci --diff` EXIT=1 in 902 s; cases=3757 pass=3521 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only | 5 born (`evalorder/unseq-addr`: 4 membership + 1 strict); 3 lane moves strict → membership (`multi-assign/deref-target-before-rhs` {828, 822, 181, 188}, `multi-assign/selector-target-before-rhs` {727, 722, 171, 177}, `channels/make-edge/ordinary-receive-eval-order` {170, 171, 182} — an `&x` argument beside a read of the address-taken variable; gc's call-first member inside each); 3752 = 3517 / 235 → 3757 = 3522 / 235 | 169 → 177 admitted (+3 widening, +5 the born package; 0 lost); probes 58 → 58 corpus, twin 128 | TRACE-LINE-D |
| `64b3757c` | **E5e** strings — `s[i]` / `s[lo:hi]` FAILING PURE OPS on the string value (E13's class on a string base), `len(s)` an E1 participant; a CLASSIFIER-ONLY widening (no core, no decoder, no schema change) | `ci --diff` EXIT=1 in 761 s; cases=3752 pass=3516 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (the binary byte-identical to E5c's) | 4 born (`evalorder/unseq-strings`: 3 membership + 1 strict); `builtins/e13-sibling-panic-order/bytes-conv-payload-vs-call` probe → graph, set reproduced; a status-diverse first row refused by name and split; 3748 = 3513 / 235 → 3752 = 3517 / 235 | 165 → 168 admitted (+1 widening, +2 the born package; 0 lost); probes 59 → 58 corpus, twin 128 | 3716 ids: 3675 SAME, 21 DIFFER (= E5a's 6 + E5b's 11 + E5c's 3 + E5e's 1 admitted sweeps' rows), 20 ONLY_B (the born rows); `unseqNext` 1482 → 1994, `unseqPanic` 204 → 168 |
| `6bf3d780` | **E5c** map literals as `allocate` bodies (`AllocSpec.mapLit`, the ratified arm mechanism) without E1 edges | `ci --diff` EXIT=1 in 909 s; cases=3748 pass=3512 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (provenance STALE `AdmissionIndices.lean`; the `google-search` drift line) | 3 born (`evalorder/unseq-maplit`: 2 membership + 1 strict); 2 lane moves strict → membership (noodler `map-literal-key-vs-call`; e13 `map-lit-payload-vs-call` — the F6 shape); 3745 = 3510 / 235 → 3748 = 3513 / 235 | 154 → 165 admitted (+2 widening, +9 the born packages; 0 lost); probes 60 → 59 corpus, twin 128 | 3712 ids: 3676 SAME, 20 DIFFER (= E5a's 6 + E5b's 11 + E5c's 3 admitted sweeps' rows), 16 ONLY_B (the born rows); `unseqNext` 1482 → 1958, `unseqPanic` 204 → 174 |
| `1a0ff398` | **E5b** multi-target assignments — tuple, blank, multi-value call, the comma-ok forms; every target a phase-1 sibling plan; `WideSpec.mapLookup`/`.typeAssert` ARMS (no new kind) | `ci --diff` run 2 EXIT=1 in 765 s, K=32; 3745 = 3509 / 236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (run 1 also red on stale native fixtures — regenerated) | 7 born (`evalorder/unseq-multi`: 5 membership + 2 strict); 4 lane moves strict → membership (BUG-052's deref-target ×2, slice-header-base; noodler rhs-list-index-call-index); the spec example red-first then PASS; 3738 = 3503 / 235 → 3745 = 3510 / 235 | 137 → 154 admitted (+12 widening, +5 E5a's package; 0 lost); probes 63 → 60 corpus, twin 128 | 3709 ids: 3679 SAME, 17 DIFFER (= E5a's 6 + E5b's 11 admitted sweeps' rows), 13 ONLY_B (the born rows); `unseqNext` 1482 → 1903, `unseqPanic` 204 → 174 |
| `732da84c` | **E5a** the reading-(a) built-ins `min`/`max`/`copy`/`append` — `min`/`max` pure E1 participants, `append`/`copy` effectful `wide` bodies (PENDING [USER], §2 item 1) | `ci --diff` EXIT=1 in 971 s, K=32; 3738 = 3502 / 236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (provenance STALE `AdmissionIndices.lean`; the `google-search` drift line) | 6 born (`evalorder/unseq-builtins`: 4 membership + 2 strict); 5 e13 rows probe → graph, sets unchanged; `copy-min` unchanged; 3732 = 3497 / 235 → 3738 = 3503 / 235 | 131 → 137 admitted (+6, 0 lost); probes 70 → 63 corpus (e13 17 → 12, copy-min 2 → 0), twin 128 | 3702 ids: 3690 SAME, 6 DIFFER (= the 6 admitted sweeps' rows), 6 ONLY_B (the born rows); `unseqNext` 1482 → 1609, `unseqPanic` 204 → 174 |

## 2. PENDING [USER] — posed, never self-adjudicated

1. **The `wide` body kind** (E5a; design §E5a): `UnseqBody.wide (binds : List String) (spec : WideSpec)` — ONE
   statement-bodied occurrence kind over a CLOSED spec (`append`, `copy`; E5b adds `mapLookup`, `typeAssert`)
   mirroring `allocate` (the body runs the hoisted wide statement with the binder cells as its targets under
   the wait frame; two Step rules `unseqRunWide`/`unseqWideDone`). Alternatives named: (a) `AllocSpec.append`/
   `.copy` arms — a misnomer for `copy`, which never allocates; (b) one body kind PER built-in — four
   constructors and eight Step rules for one shape. [AGENT] choice: the one closed kind. RATIFICATION at the
   merge ask.
2. **The trigger and E6** (design §0): retiring the legacy probe under the RATIFIED trigger («unordered against
   an EFFECTFUL event») would NARROW the ~30 panic-vs-panic rows with no effectful event (`iv.(int) +
   len(make([]int, t[k]))` and kin) from two members to one. A refinement — «unordered against an effectful
   event OR against another FAILING occurrence» (panic identity is an observable) — is a change to ratified
   item 2 and is POSED here, not taken; with it, E6 still waits on the non-main-unit emitters (item 3).
4. **Audit F8 — an `after` edge on a literal `allocate` decodes** (E5c touched the decoder's `allocate` rules — the `map-lit`
   arm): the wire still does not express the lowering's «no E1 edge on literals» policy; making it a NAMED refusal at
   decode (the frontend never emits such an edge; a hand-built or forged wire could) is a design choice POSED here, not
   taken. Alternative: leave it a lowering-only policy (the audit's own disposition: a design fact, not a defect).
3. **Non-main units and E6** (design §0): 128 of the twin's probes and 12 of the corpus's sit in imported source
   units the whole-sweep grammar refuses by design. E6's zero condition is unreachable without lowering those
   units as graphs — a grammar widening the brief forbids «merely to reach zero». POSED: whether the next lane
   widens the grammar to non-main units (the twin re-pins) or E6 is re-scoped to the main unit.

## 3. What remains — E6's census

E6 NOT entered (the census is not zero). Residual legacy `unseq-probe` emitters, by reason and count, at the
lane's tip: (filled at park).

## 4. Whole-corpus choice traces

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5a.txt`: main `d76721bd` vs the E5a commit `732da84c` — 3702 ids, 3690 byte-identical, 6 DIFFER (exactly the six sweeps E5a admits: the five e13 built-in rows and `slices/copy-min`), 6 only on the E5a side (the born rows); site census `unseqNext` 1482 → 1609, `unseqPanic` 204 → 174 — the legacy probe is still consulted on 174 recorded consumptions (E6 not reachable; §2/§3).

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5b.txt`: main `d76721bd` vs the E5b commit `1a0ff398` — 3709 ids, 3679 byte-identical, 17 DIFFER (exactly the rows of E5a's six and E5b's eleven admitted sweeps — the multi-assign family incl. BUG-052's rows and the spec's own example), 13 only on the E5b side (the born rows); site census `unseqNext` 1482 → 1903, `unseqPanic` 204 → 174 (unchanged from E5a); 34 export refusals and the exhausted-stream lists identical on both sides.

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5c.txt`: main `d76721bd` vs the E5c commit `6bf3d780` — 3712 ids, 3676 byte-identical, 20 DIFFER (exactly the rows of E5a's six, E5b's eleven and E5c's three admitted sweeps), 16 only on the E5c side (the born rows); site census `unseqNext` 1482 → 1958, `unseqPanic` 204 → 174 (unchanged from E5a); 34 export refusals and the exhausted-stream lists identical on both sides.

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5e.txt`: main `d76721bd` vs the E5e commit `64b3757c` — 3716 ids, 3675 byte-identical, 21 DIFFER (exactly the rows of E5a's six, E5b's eleven, E5c's three and E5e's one admitted sweeps), 20 only on the E5e side (the born rows); site census `unseqNext` 1482 → 1994, `unseqPanic` 204 → 168; 34 export refusals and the exhausted-stream lists identical on both sides.

## 6. Operational notes for the next session

- Scratch under the worktree's `.tmp/` (gitignored): `.tmp/census/{run.sh,summarize.py,diff.py}` (Stage E's
  census tooling, copied), `.tmp/census/probes.sh` + `probe-sites.py` (NEW — the legacy PROBE EMISSION census:
  emit every corpus package's wire + the twin with a given frontend, count `unseq-probe` / `unseq` nodes per
  package; per-function emitters with the probed head kinds), `.tmp/trace-compare.py` (Stage D's per-id
  byte-identity), `.tmp/nativefrontend-main` + `.tmp/golean-main` (main's binaries: the frontend built from
  this tree at the branch point, the golean binary = the warmed `.lake/build/bin/golean`), `.tmp/e5/` (the
  families' replayable edit scripts, gate scripts, gc drivers).
- The gate lock protocol: atomic `mkdir /home/dev/projects/golean/artifacts/build-lock.d` at the PRIMARY root,
  an owner file, trap-protected release, wait-retry every 120 s — never take over a live lock.
- Never edit the tree while a gate or a trace reads it.

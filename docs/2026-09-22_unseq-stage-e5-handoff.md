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
| (E5a, this tree) | **E5a** the reading-(a) built-ins `min`/`max`/`copy`/`append` — `min`/`max` pure E1 participants, `append`/`copy` effectful `wide` bodies (PENDING [USER], §2 item 1) | `ci --diff` EXIT=1 in 971 s, K=32; 3738 = 3502 / 236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (provenance STALE `AdmissionIndices.lean`; the `google-search` drift line) | 6 born (`evalorder/unseq-builtins`: 4 membership + 2 strict); 5 e13 rows probe → graph, sets unchanged; `copy-min` unchanged; 3732 = 3497 / 235 → 3738 = 3503 / 235 | 131 → 137 admitted (+6, 0 lost); probes 70 → 63 corpus (e13 17 → 12, copy-min 2 → 0), twin 128 | TRACE-LINE |

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
3. **Non-main units and E6** (design §0): 128 of the twin's probes and 12 of the corpus's sit in imported source
   units the whole-sweep grammar refuses by design. E6's zero condition is unreachable without lowering those
   units as graphs — a grammar widening the brief forbids «merely to reach zero». POSED: whether the next lane
   widens the grammar to non-main units (the twin re-pins) or E6 is re-scoped to the main unit.

## 3. What remains — E6's census

E6 NOT entered (the census is not zero). Residual legacy `unseq-probe` emitters, by reason and count, at the
lane's tip: (filled at park).

## 4. Whole-corpus choice traces

(filled per family)

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

# Stage E5 of the evaluation-order model v2.1 — lane handoff (`core/unseq-stage-e5-0922`)

[AGENT] worker, 2026-09-22. Worktree `.claude/worktrees/unseq-stage-e5`, branch `core/unseq-stage-e5-0922`,
based on main `d76721bd` (train r46's 5a records) and REBASED onto main's records-only close `dc5de785` at the lane's end
(a clean rebase; the five commits' hashes below are post-rebase — the evidence files cite the pre-rebase ones, map in §6). Brief: the Stage E handoff §3 (`docs/2026-09-21_unseq-stage-e-handoff.md`)
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
| `5570a190` | **E5d** the ADDRESS of a variable as an operand — an address formation (no read, no failure), NO occurrence; an ALLOWED LIST of value positions (argument, receiver, payload, plain stored value, return, tuple beside no planned target); the decoder gains ONE payload arm (`ref`/`globaladdr`; `ref $cell` refused — F2); no core change | `ci --diff` EXIT=1 in 902 s; cases=3757 pass=3521 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only | 5 born (`evalorder/unseq-addr`: 4 membership + 1 strict); 3 lane moves strict → membership (`multi-assign/deref-target-before-rhs` {828, 822, 181, 188}, `multi-assign/selector-target-before-rhs` {727, 722, 171, 177}, `channels/make-edge/ordinary-receive-eval-order` {170, 171, 182} — an `&x` argument beside a read of the address-taken variable; gc's call-first member inside each); 3752 = 3517 / 235 → 3757 = 3522 / 235 | 169 → 177 admitted (+3 widening, +5 the born package; 0 lost); probes 58 → 58 corpus, twin 128 | 3721 ids: 3672 SAME, 24 DIFFER (= E5a's 6 + E5b's 11 + E5c's 3 + E5e's 1 + E5d's 3 admitted sweeps' rows), 25 ONLY_B (the born rows); `unseqNext` 1482 → 2101, `unseqPanic` 204 → 168 |
| `6f6244f0` | **E5e** strings — `s[i]` / `s[lo:hi]` FAILING PURE OPS on the string value (E13's class on a string base), `len(s)` an E1 participant; a CLASSIFIER-ONLY widening (no core, no decoder, no schema change) | `ci --diff` EXIT=1 in 761 s; cases=3752 pass=3516 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (the binary byte-identical to E5c's) | 4 born (`evalorder/unseq-strings`: 3 membership + 1 strict); `builtins/e13-sibling-panic-order/bytes-conv-payload-vs-call` probe → graph, set reproduced; a status-diverse first row refused by name and split; 3748 = 3513 / 235 → 3752 = 3517 / 235 | 165 → 168 admitted (+1 widening, +2 the born package; 0 lost); probes 59 → 58 corpus, twin 128 | 3716 ids: 3675 SAME, 21 DIFFER (= E5a's 6 + E5b's 11 + E5c's 3 + E5e's 1 admitted sweeps' rows), 20 ONLY_B (the born rows); `unseqNext` 1482 → 1994, `unseqPanic` 204 → 168 |
| `f5903528` | **E5c** map literals as `allocate` bodies (`AllocSpec.mapLit`, the ratified arm mechanism) without E1 edges | `ci --diff` EXIT=1 in 909 s; cases=3748 pass=3512 fail=236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (provenance STALE `AdmissionIndices.lean`; the `google-search` drift line) | 3 born (`evalorder/unseq-maplit`: 2 membership + 1 strict); 2 lane moves strict → membership (noodler `map-literal-key-vs-call`; e13 `map-lit-payload-vs-call` — the F6 shape); 3745 = 3510 / 235 → 3748 = 3513 / 235 | 154 → 165 admitted (+2 widening, +9 the born packages; 0 lost); probes 60 → 59 corpus, twin 128 | 3712 ids: 3676 SAME, 20 DIFFER (= E5a's 6 + E5b's 11 + E5c's 3 admitted sweeps' rows), 16 ONLY_B (the born rows); `unseqNext` 1482 → 1958, `unseqPanic` 204 → 174 |
| `f70903dc` | **E5b** multi-target assignments — tuple, blank, multi-value call, the comma-ok forms; every target a phase-1 sibling plan; `WideSpec.mapLookup`/`.typeAssert` ARMS (no new kind) | `ci --diff` run 2 EXIT=1 in 765 s, K=32; 3745 = 3509 / 236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (run 1 also red on stale native fixtures — regenerated) | 7 born (`evalorder/unseq-multi`: 5 membership + 2 strict); 4 lane moves strict → membership (BUG-052's deref-target ×2, slice-header-base; noodler rhs-list-index-call-index); the spec example red-first then PASS; 3738 = 3503 / 235 → 3745 = 3510 / 235 | 137 → 154 admitted (+12 widening, +5 E5a's package; 0 lost); probes 63 → 60 corpus, twin 128 | 3709 ids: 3679 SAME, 17 DIFFER (= E5a's 6 + E5b's 11 admitted sweeps' rows), 13 ONLY_B (the born rows); `unseqNext` 1482 → 1903, `unseqPanic` 204 → 174 |
| `eba20f2d` | **E5a** the reading-(a) built-ins `min`/`max`/`copy`/`append` — `min`/`max` pure E1 participants, `append`/`copy` effectful `wide` bodies (PENDING [USER], §2 item 1) | `ci --diff` EXIT=1 in 971 s, K=32; 3738 = 3502 / 236 in the run = the pin with the one 5a-class row red; red = the 5a pair only (provenance STALE `AdmissionIndices.lean`; the `google-search` drift line) | 6 born (`evalorder/unseq-builtins`: 4 membership + 2 strict); 5 e13 rows probe → graph, sets unchanged; `copy-min` unchanged; 3732 = 3497 / 235 → 3738 = 3503 / 235 | 131 → 137 admitted (+6, 0 lost); probes 70 → 63 corpus (e13 17 → 12, copy-min 2 → 0), twin 128 | 3702 ids: 3690 SAME, 6 DIFFER (= the 6 admitted sweeps' rows), 6 ONLY_B (the born rows); `unseqNext` 1482 → 1609, `unseqPanic` 204 → 174 |

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
3. **Non-main units and E6** (design §0): 128 of the twin's probes and 23 of the corpus's (at the tip, §3) sit in imported source
   units the whole-sweep grammar refuses by design. E6's zero condition is unreachable without lowering those
   units as graphs — a grammar widening the brief forbids «merely to reach zero». POSED: whether the next lane
   widens the grammar to non-main units (the twin re-pins) or E6 is re-scoped to the main unit.
4. **Audit F8 — an `after` edge on a literal `allocate` decodes** (E5c touched the decoder's `allocate` rules — the `map-lit`
   arm): the wire still does not express the lowering's «no E1 edge on literals» policy; making it a NAMED refusal at
   decode (the frontend never emits such an edge; a hand-built or forged wire could) is a design choice POSED here, not
   taken. Alternative: leave it a lowering-only policy (the audit's own disposition: a design fact, not a defect).
5. **E2/E12's VALUE axis — (a) ENVELOPED on this lane's rows.** Ratified item 3 (2026-09-22) moves E2/E12 (b) → (a) ONLY on
   NAMED rows. Every membership row this lane BORE or MOVED carries the (a) envelope (the mutable read before / after the
   sibling call, gc's draw one member): E5a `evalorder/unseq-builtins/{min-read-vs-call, append-read-vs-call,
   copy-effect-vs-read, append-spread-str-vs-call}`; E5b `evalorder/unseq-multi/{tuple-header-vs-call, blank-panic-vs-call,
   comma-ok-recv-target-vs-panic, multi-call-header-vs-call, define-tuple-vs-call}` and the moved `multi-assign/call-write-back-
   order/{deref-target, slice-header-base}`, `multi-assign/call-write-back-order-value/deref-target`, `noodler/latitude/rhs-list-
   index-call-index`; E5c `evalorder/unseq-maplit/{map-lit-entry-vs-call, map-lit-key-vs-call}` and the moved `noodler/latitude/
   map-literal-key-vs-call`, `builtins/e13-sibling-panic-order/map-lit-payload-vs-call`; E5e `evalorder/unseq-strings/{str-index-
   vs-call, str-slice-vs-call, str-index-panic-vs-print}`; E5d `evalorder/unseq-addr/{addr-arg-vs-read, addr-payload-vs-call,
   addr-stored-vs-read, addr-global-arg-vs-read}` and the moved `multi-assign/deref-target-before-rhs`, `multi-assign/selector-
   target-before-rhs`, `channels/make-edge/ordinary-receive-eval-order`. POSED: ratify this row list as the named (a) rows (the
   inventory's E2/E12 bullets carry each with its set and gc's member); the entries themselves stay (b) PINNED.

## 3. What remains — E6's census

E6 NOT entered: the legacy `unseq-probe` emission census at the lane's tip (`probes-e5d.txt`, the E5d frontend) is **58 in the
corpus (17 packages) + 128 in the raft twin**, from 70 + 128 at the branch point (E5a −7, E5b −3, E5c −1, E5e −1; E5d 0). By
reason, the residue the whole-sweep grammar does not reach and the trigger does not admit:

| class | count | what would reach it |
|---|---|---|
| NON-MAIN UNITS — imported / library source units the whole-sweep grammar refuses by design (the twin's 128, all `field-get`; the corpus's `stdlib-source/{errors-join 5, strconv-parseuint 4, errors-wrap 3, frontier 3}`, `multipkg/mini-raft-twin` 7, `imported-goose/generics/generic-conversion` 1) | 128 twin + 23 corpus | lowering non-main units as graphs — a grammar widening the brief forbids «merely to reach zero»; POSED (§2 item 3) |
| PANIC-vs-PANIC pairs with no effectful event under the RATIFIED trigger — a type assertion / index beside `make`/`len`/`new` (`builtins/len-vs-call-order`: 15, thirteen `type-assert`, two `index-get`; `e13-sibling-panic-order`'s `assertLeftMakeSlice`, `tgtAssertVsMake`, `convLeftCall`, `ifaceCmpLeftCall`, `sendChanIndex`, `assertReturnList$lit0`: 6) | 21 corpus | the trigger refinement («… OR against another FAILING occurrence»), a change to ratified item 2 — POSED (§2 item 2) |
| SHAPES outside the grammar — `&a[i]` (an `index-addr` head: the address of an ELEMENT, not of a variable — E5d admits `&x` only; e13's `addrIndexLeftLenHoist`, `addrAssertLeftCall`, `arrayBaseTargetVsLen`: 3), `recover()` inside a lifted body (e13's `recoverAssertVsLen$lit0`, `recoverAssertVsCallW$lit2`: 2), a generic instantiation's key (`len-vs-call-order/makeHintGenericKey[…]`: 2 — counted above) | 5 corpus | a later family per shape (the element address is E5z's `&a[i]`/`&s.f` axis, design §E5z) |
| the SINGLETONS across `channels/{recv-edge, recv-map-elem}`, `fmt/sprintf-dyn`, `noodler/{frontier2 ×2, misc, strings}`, `panic-recover/shim-refusal-unrecoverable`, `strconv/format-parse` (heads `type-assert`, `field-get`, `index-get`) | 9 corpus | per-function reasons in `probes-e5d.txt`'s emitter list; mostly library-typed operands (`error`, `bytes.Buffer`) and callee shapes outside the grammar |

The whole-sweep census at the tip (`census-e5d.txt`): 108 236 sweeps, **177 admitted** (131 at the branch point), all in main
units; the main-unit legacy first reasons are led by «no call occurrence» (40 141 — call-free sweeps, nothing to reorder
against), «statement form outside the pilot grammar» (33 388), non-main-package callees (4 991 + 3 062 + 1 757), «no
non-event occurrence beside the call(s)» (3 253 — all-forced), «bare return» (1 768), result / target types outside the
grammar (`error` 1 579 + 751, `float64` 299 + 288), generic callees (1 266), `panic` statements (1 137), captured targets
written through a pointer parameter in a lifted body (662), «no occurrence observable against an effectful event» (608 —
the trigger's own forced class), string types outside the grammar (`untyped string` 514), arrays as index bases (499 +
323 + 198). None of these is an E5 family's residue; each is a grammar axis of its own (design §E5z).

Deferred families (design §E5z): floats (254 main-unit sweeps — a Platform contract, not a grammar hole), the element /
field address `&a[i]`/`&s.f`, arrays as index bases, the non-main-unit grammar, the trigger refinement.

## 4. Whole-corpus choice traces

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5a.txt`: main `d76721bd` vs the E5a commit `732da84c` — 3702 ids, 3690 byte-identical, 6 DIFFER (exactly the six sweeps E5a admits: the five e13 built-in rows and `slices/copy-min`), 6 only on the E5a side (the born rows); site census `unseqNext` 1482 → 1609, `unseqPanic` 204 → 174 — the legacy probe is still consulted on 174 recorded consumptions (E6 not reachable; §2/§3).

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5b.txt`: main `d76721bd` vs the E5b commit `1a0ff398` — 3709 ids, 3679 byte-identical, 17 DIFFER (exactly the rows of E5a's six and E5b's eleven admitted sweeps — the multi-assign family incl. BUG-052's rows and the spec's own example), 13 only on the E5b side (the born rows); site census `unseqNext` 1482 → 1903, `unseqPanic` 204 → 174 (unchanged from E5a); 34 export refusals and the exhausted-stream lists identical on both sides.

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5c.txt`: main `d76721bd` vs the E5c commit `6bf3d780` — 3712 ids, 3676 byte-identical, 20 DIFFER (exactly the rows of E5a's six, E5b's eleven and E5c's three admitted sweeps), 16 only on the E5c side (the born rows); site census `unseqNext` 1482 → 1958, `unseqPanic` 204 → 174 (unchanged from E5a); 34 export refusals and the exhausted-stream lists identical on both sides.

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5e.txt`: main `d76721bd` vs the E5e commit `64b3757c` — 3716 ids, 3675 byte-identical, 21 DIFFER (exactly the rows of E5a's six, E5b's eleven, E5c's three and E5e's one admitted sweeps), 20 only on the E5e side (the born rows); site census `unseqNext` 1482 → 1994, `unseqPanic` 204 → 168; 34 export refusals and the exhausted-stream lists identical on both sides.

`docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5d.txt`: main `d76721bd` vs the E5d commit (`50fdf05e` pre-rebase = `5570a190`) — 3721 ids, 3672 byte-identical, 24 DIFFER (exactly the rows of the sweeps E5a–E5e admit — E5d's three the former strict pins), 25 only on the E5d side (the born rows); site census `unseqNext` 1482 → 2101, `unseqPanic` 204 → 168; 34 export refusals and the exhausted-stream lists identical on both sides. Outside the admitted families every id of every trace is byte-identical to main's.

## 5. The gate at the rebased tip

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the rebased tip (E5d's content on main `dc5de785`; the box-wide lock 2026-09-22T04:38:01Z–2026-09-22T04:50:53Z): EXIT=1 in 772 s; `cases=3757 pass=3521 fail=236` = the pin 3522 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for `GoLean/GoCore/AdmissionIndices.lean`; the one `imported-goose/channel/google-search` drift line); every other step ok (`ci-diff-park.tail.txt`).

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
- `.tmp/e5/diff-one-run.sh <ids-file> <log>` runs `scripts/diff-one` on ids listed one per line under BASH — zsh does NOT
  word-split an unquoted `$var`, so `scripts/diff-one $ids` from the zsh tool shell passed one 68-line id (the manifest's
  «no executable case id» names the whole blob). A single-row package's id is the bare package path (no `/-`).
- The membership lane REFUSES a status-diverse set by name («member … has status ok, outside the case's declared status set
  [panic]») unless the row declares `ok,panic` — audit F8's mechanism, unused by every corpus row; E5e split the row instead.
- Feature tags are validated against `Corpus/coverage/tags.tsv` (`addressability`, `literals`, `globals`, `pointers` …); an
  unknown tag refuses the whole manifest before any row runs.
- Take the census AFTER the last corpus edit of a family: E5e's census preceded its row split and recorded 168 where the
  commit holds 169 (corrected at E5d).
- A whole-corpus trace takes ~25 min per side at `--jobs 5`; its results files fill progressively — completion is the
  `choice-trace-corpus: FINDINGS present` line in the nohup log AND the `exhausted-*.tsv` files present (a comparison run
  before that reports phantom `ONLY_A` ids). `K=32` in the gate paragraphs is the membership lane's draw count.
- The binaries: `.tmp/golean-e5c` = `.tmp/golean-e5e` (`c8613c32…`, no decoder change at E5e); `.tmp/golean-e5d`
  (`2159163d…`, the payload arm); the export trees `.tmp/e5{a,b,c,e,d}-tree` with their traces under `.tmp/trace`.
- Commit hashes, pre-rebase → post-rebase (the rebase onto `dc5de785` brought in ONE records-only commit — `docs/evidence/2026-09-21_unseq-stage-e/README.md`, never touched here): E5a `732da84c` → `eba20f2d`, E5b `1a0ff398` → `f70903dc`, E5c `6bf3d780` → `f5903528`, E5e `64b3757c` → `6f6244f0`, E5d `50fdf05e` → `5570a190`.

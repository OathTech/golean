# THE LAUNCH-AUDIT DOSSIER (2026-08-21)

**What this is.** The proof-campaign constitution
(`docs/2026-08-21_raft-proof-constitution.md`, `proof-constitution` lane,
branch-state at drafting) makes a comprehensive whole-stack Q/A audit a
CONSTITUTIONAL precondition of campaign launch: *"the campaign may not
start without it having run."* That audit reviews the INTEGRATED state as
a composed claim chain at one settled tip — distinct in kind from the
per-arc audits, which review diffs.

This dossier is that audit's **input**, not its output. It is built in
advance so the audit spends its skepticism on judgment (is the claim
adequate? does the chain compose?) instead of on discovery (what is the
claim? where is the evidence? what is already known-open?). It states,
per link: the CLAIM, the EVIDENCE ARTIFACTS with the gate or theorem that
verifies each, and the KNOWN BOUNDS AND RESIDUALS. It fixes nothing.

**Standing.** This document has no authority. It records the state; the
audit rules on it, and Mike rules on the audit. Where it reports a
DISCREPANCY, that is raw material with a severity GUESS — not a verdict,
not a work order, and explicitly not a licence for anyone to "clean up"
a record before the audit has seen it (a laundered record is worse than
a wrong one). Nothing in §2 was corrected; every finding is left standing
in the tree exactly as found.

**Tip.** `audit-prep` @ `521f5b57`, which is also `main`'s tip at
drafting. Three lanes were live beside this one (`w32-5b`, `w32-qrows`,
`raft-w43`); anything cited from another lane is marked BRANCH-STATE and
must be re-checked when consumed. Numbers are derivation-anchored: every
count below names the command or the tool check that produced it.

**Structure.** §1 is the claim-chain map, one section per bullet of the
constitution's launch-gate clause — six links. §2 is the mechanical
pre-reconciliation (`tools/reconcile-records`). §3 is the residuals
register. §4 is the proposed audit structure, sized against what §1–§3
found.

---

## §0 How to read the chain

The chain the campaign will hang a theorem on runs:

```
  the Go spec  --L1-->  the machine  --L2-->  the twin  --L3-->  a statement
                            ^                                        ^
                            |                                        |
                        L4 the instruments (what keeps each link honest)
                        L5 the records     (what each link claims, written down)
                        L6 the machinery   (what makes the campaign able to run at all)
```

L1–L3 are the substantive links; L4–L6 are the links that make L1–L3
believable. The constitution's six bullets are exactly these six, and
this dossier is structured by them.

Three standing readings govern every link and are not re-argued below:

1. **The two bounds** (`docs/2026-08-11_essence-of-go-doctrine.md`).
   Differential testing is the LOWER bound — its whole meaning is
   membership, `observed ∈ modeled`. The spec, memory model, docs and
   deployed-code corpus argue the UPPER bound. A green differential
   never argues width; only review does.
2. **The dumb-statement ideology** (constitution §3, Mike 2026-08-21).
   Statements read over the slow-obviously-correct semantics; every
   accelerator sits outside the TCB behind a kernel-checked equality.
   The corollary that directs audit effort: *the observation notion is
   load-bearing* — statement-adequacy review is where skepticism
   belongs, because aboutness is the one thing no kernel checks.
3. **Green is not correctness; the failing-set diff is.** A green gate
   proves elaboration and non-regression. The classes it structurally
   cannot see are enumerated per instrument in §1.4.

---

## §1 THE CLAIM-CHAIN MAP

### §1.1 LINK 1 — spec → machine (the accounting chain)

#### The claim

Not "the machine matches Go". The claim is a two-bounds claim with an
enumerated debt register:

> "**A trustworthy, portable Go semantics** — not a model of any
> particular implementation, test suite, or scheduler. The machine we
> want is the WEAKEST machine that Go can plausibly ever do: the
> semantics that exercises *all* degrees of freedom latent in the
> language."
> — `docs/2026-08-11_essence-of-go-doctrine.md:10-13`

> "**Differential testing establishes the LOWER bound.** … Its entire
> meaning is membership: real Go behavior ∈ modeled Go behavior. The
> oracle can never validate the model's width."
> — `docs/2026-08-11_essence-of-go-doctrine.md:22-30`

Coverage is claimed against the PINNED SPEC, not against the corpus:

> "**This file IS the repo's coverage claim**: coverage is measured
> against the PINNED SPEC (go1.26.5, `docs/spec-sources.md`), not
> against what the corpus happens to try."
> — `docs/language-coverage-ledger.md:6-8`

Scope: **GoCore models the Go 1.26 language**
(`docs/2026-08-11_essence-of-go-doctrine.md:60`).

#### Evidence artifacts

**Mechanically enforced** — a `scripts/` gate reads the file and fails
on it:

| artifact | what it is | enforcing gate |
|---|---|---|
| `baselines/native-full.tsv` | tracked full-corpus differential baseline (`result`/`id`/`stage`), dated header + re-pin reason | `scripts/coverage-baseline-diff` (`scripts/ci` "differential baseline diff") |
| `baselines/negative-full.tsv` | compile-rejection baseline, 390 cases, all PASS | `scripts/ci` "negative baseline diff" |
| `baselines/untriaged-ids` | `<id><TAB><disposition>` over {coverage, latitude, wrong-answer} | `scripts/check-bugs.sh` check 4b (set ratchet) |
| `baselines/untriaged-count` | per-class ceilings | `scripts/check-bugs.sh` check 4 (count ratchet) |
| `docs/BUGS.md` | the single canonical fidelity-bug index | `scripts/check-bugs.sh` checks 0–3 |
| `baselines/certified/*.certified.tsv` | the one `tier=slow` certified observation set, wire-hash-guarded | `scripts/ci --slow` re-enumerates; fast runs report `CERTIFIED-CACHED` |
| `baselines/golden/*.repr`, `hidden-dep-order.observation.json` | golden lowered `Program` terms + the E7 deviation pin | `scripts/check-golden`, `scripts/check-imported-pins` |
| `deps/go` @ go1.26.5, cited as `spec#…`/`mem#…` | the pinned normative text | `scripts/check-spec-anchors` — **resolution only** |
| `docs/spec-sources.md` | the authoritative pin index | read by check-spec-anchors, setup-deps, CI |
| `Corpus/coverage/tags.tsv` | canonical feature vocabulary | `scripts/check-coverage` (a canonical tag with no case is fatal) |

**Hand-curated — NO script reads them.** Verified by `grep -rl <name>
scripts/ .github/`: `docs/2026-08-11_latitude-inventory.md`,
`docs/spec-interpretations.md`, `docs/spec-divergence-ledger.md`,
`docs/language-coverage-ledger.md`, `docs/coverage-ledger.md`, both
doctrine notes, and the covmap CIP drafts. Three of these appear in
`scripts/` only inside COMMENTS. **This is the single most important
structural fact about link 1**: the entire accounting chain above the
baseline — the ledgers that say what the reds MEAN — rests on review
alone. `tools/reconcile-records` (§2) exists because of exactly this,
and it found real drift on the first run.

Notably, `docs/language-coverage-ledger.md:457-458` claims its red
mapping was "verified mechanically at the re-pin". **No such script
exists in `scripts/`.** The verification was real (it was done); the
mechanism was not retained, so it cannot re-run — which is why the claim
no longer holds at this tip (§2, findings R-2 and R-3).

**Theorem-discharged on this link: exactly one entry.**
`Frame.allocatorIndependence` over `execStmtLoop_ren` discharges C11
(allocation addressing) as class **(q) ENVELOPE-BY-QUOTIENT**
(`docs/2026-08-11_latitude-inventory.md:429-444`; doctrine register #6).
Every other latitude point is carried by curated prose plus a corpus
pin, or by nothing.

#### Counts at the tip

Derived by `tools/reconcile-records` and by `grep -v '^#' … | awk`:

| quantity | value |
|---|---|
| baseline cases | **2343** (2199 PASS / 144 FAIL) |
| — PASS by lane | 2098 strict, 57 confluent, 23 membership, 21 racy |
| — FAIL by stage | 118 frontend-export, 17 lean-observation, 6 differential, 1 nondet, 1 membership, 1 confluent |
| fidelity-stage FAILs (non-frontend-export) | **26** = 15 untriaged + 11 pinned by open bugs |
| negative baseline | 390 cases, 390 PASS (recorded 2026-08-18) |
| untriaged tracked | **15** — coverage 11, latitude 4, **wrong-answer 0**; ceilings equal actuals |
| certified sets | 1 record, 6 member rows (`imported-goose/channel/google-search`) |
| latitude inventory | **39** rows (C1–C11, E1–E13, R1–R15) |
| divergence ledger | **15** entries L-001…L-015 (4 spec-ambiguity, 3 spec-bug, 2 gc-bug, 2 prior-art, 3 informational, 1 absence-record) |
| interpretations index | **7** rows I-1…I-7, each backed by a distinct L-entry |
| language-coverage ledger | 158 spec sections (A 30 / B 80 / D 28 / frontier 2 / out-of-language 18), 18 mem sections, 15 FR rows, 10 Q rows, 7 T rows |
| coverage ledger | 34 area rows (partial 23, active 7, deferred-nondet 2, deferred-stdlib 1, deferred-unsafe 1) |
| open bugs | **8** (BUG-002, 004, 008, 041, 059, 061, 062, 065) |

**Provenance caveat, stated up front because it governs every number
above.** The branch tip's gate ran at `200235fd` under
`GOLEAN_ALLOW_NO_DIFF=1` (a legitimate docs-only hatch), so these counts
are read off the TRACKED BASELINE recorded 2026-08-21 by the holes arc,
not off a differential run at this tip. **The audit should require one
full `scripts/ci --diff` at the settled tip before it opens** — the
baseline is a record of a run, and "the record still matches the tree"
is the one thing no reading can establish.

#### Known bounds and residuals

**(a) The structural limit of the lower bound.** The differential is
membership only: *"No amount of green can validate the model's WIDTH"*
(`docs/2026-08-04_nondeterminism-doctrine.md:34-35`). Too-wide is
undetectable by any oracle — *"go run cannot demonstrate a behavior it
never has"* (`:179-181`). At a PINNED latitude point a green tells you
*"nothing beyond 'the pin reproduces gc here' (never that the pin is
right to exist)"* (`:557-559`). Per-lane blindness is captioned in the
same note: strict is blind to schedule effects; confluent/membership are
scoped to the registry-point path set and cannot speak below registry
granularity; litmus cannot exhibit weak-memory behaviors because those
programs are refused.

**(b) Evidence-base narrowness** (the doctrine's register):
- **One implementation** — register #3: the oracle is gc at a pinned
  version; no cross-implementation lane exists.
- **One platform** — inventory register #9: linux/amd64 at default
  GOAMD64; gc/arm64 executions of fusable shapes are already outside
  the float envelope.
- **XIMPL and ARCH evidence classes: zero work done**
  (`docs/2026-08-11_latitude-inventory.md:58-62`).
- **N=1 verdict discipline** — kind-attribution at N=1 is ARGUED, never
  voted (`docs/spec-divergence-ledger.md:29-32`).

**(c) The version pin's third leg does not exist.** Spec `go1.26.5` +
oracle `go1.26.5 linux/amd64`; but *"the corpus has no `go.mod`, so 'the
corpus's `go` directive must agree' has no object today"*
(`docs/spec-sources.md`). The preflight is spec-pin ⟷ oracle only.

**(d) The anchor lint is resolution-only.** `scripts/check-spec-anchors`
states its own limit: it *"cannot see a resolving anchor attached to a
misquoted or stale clause text"* (`:28-30`). The P2 audit found **five
such misquotes** the lint structurally cannot see. L-006 is the tripwire
lesson: go_mem commit `977e23a707` added normative text with the anchor
set and version line byte-identical. The covmap content-hash layer that
would close this is **validated but NOT wired**, blocked on CIP-1; all
four CIP drafts are marked "not yet handed to the covmap repo". The
R-series of the inventory is not anchor-retrofitted.

**(e) Pinned latitude with live re-envelope obligations** — the debt
list, priority-ordered (`docs/2026-08-11_latitude-inventory.md:1158-1204`):
E7 hidden-dep init order (known ≠ gc, **UNGUARDED** — no frontend check
detects the shape, and `etcd-io/raft` has package-level vars); R3
`[]byte(s)` capacity (gc outside the singleton on the escaping path, and
the rune arm has NO agreeing pin at all); E3/E4/E5 unordered-panic
selection axes (gc's realization compiler-internal, hence UNPINNABLE);
E13 (assertion axis realizes a different member than gc — *"NO PIN MAY
BE TAKEN HERE"*, census row only); R15 zero-size address identity
(standing differential RED); E9's cross-goroutine delete-prune residual;
C7's woken-select narrowing (on an "[ANALYSIS], not a theorem"
argument); C3's B3 abort window; C2's registry/back-edge granularity
(register #5's residual).

**(f) Standing idealizations and refusals.** Unbounded memory /
allocation never fails (register #7 — STANDING IDEALIZATION, no
obligation). SC-only within DRF; racy programs refused (register #4).
Six refusals standing in for latitude (§5 of the inventory) — *"none is
a fidelity achievement"*. The detector scope ledger's U2/U4/U5/O1, and
register #13: *"the race-refusal boundary is TSan's realized edge set,
not go_mem's minimal relation."*

**(g) Open unknowns, class (d)**: U-2 (L4 ⊆ L1 reachability — no theorem
and no counterexample search), U-3, U-4 (owed differential coverage),
U-5 (wide-op granularity re-audit still owed), U-6, U-7 (*"the inventory
ASSUMES the version-tracking pins actually fire on toolchain movement —
believed true, not re-audited"*).

**(h) The load-bearing open bug on this link is BUG-062** — a
forced-point silent wrong answer (`docs/BUGS.md:2941-2957`, "machine 3
vs go 1 on both pinned rows") that is **known-incomplete at this tip**:
grossmith campaign 2's follow-up F-1 (widen the statement past
`len`/`cap` to the `min`/`max` value divergence) and F-2 (five offered
corpus rows) are both OPEN.

**(i) External differential evidence and its limits.** Grossmith
campaign 2 (2026-08-20): 79,800 judged programs, 3 observation
mismatches + 2 reference build failures, and *"the differential oracle
was wrong more often than the machine was"*. Its own stated coverage
limit is the sharpest sentence on this link: the generator emits no
pointers, channels, floats, complex, runes, unsafe, goto, generics,
imports or `func init`, and maps never under mutation, so *"every
concurrency-, pointer-, float- and package-structure-related open item …
is untouched by this campaign … A clean sweep here says nothing about
them."*

**(j) Frontier / unexercised language surface.** 118 frontend-export
reds across 15 FR rows (largest: FR-15 complex 27, FR-12 range-over-func
9, FR-13 anonymous-struct TypeIds 8). 10 concurrency-entangled design
questions, 21 reds, none queued. 7 sufficiency-gap T rows. 80 of 149
graded rows are grade **B** — *"green is strong evidence, not an
implication"* — and the 28 grade-D rows are DELEGATED to go/types
upstream of both sides, with the caveat that constant-heavy greens
attest go/constant folding, **not GoCore arithmetic**.

**(k) Records-vs-code flags the inventory carries about itself**
(`:1288-1317`): a stale `Race.lean` docstring; the int-width pin having
no site-level record; a doctrine-wording correction.

**(l) Outward-facing debt.** L-007/L-008 spec errata UNREPORTED; L-010
in the same bundle; L-014 gc-bug filing pending Mike; L-015 recorded,
not filing. Named high-value curation targets not done (golang/go
discussions #47141, #56010; `Package_unsafe`; Go 101 seed #3). Spec-truth
P5 unexecuted; OQ3 (upstream-filing policy) still open.

---

### §1.2 LINK 2 — machine → twin (the raft agreement evidence)

#### The claim, at three different strengths

**PROVED: nothing.** There is no Lean statement, theorem, or predicate
about raft Agreement anywhere in the tree. `scripts/check-raft-goal` —
the unforgeable completion predicate the P0 scoping doc §4.1 demands —
**does not exist** (verified: `ls scripts/check-raft-goal` → no such
file). The pinned Lean statement is master-plan milestone **M5**, and the
plan says so: *"It deliberately does NOT cover proving the theorem …
this plan's end state is the push's *starting gun*"*
(`docs/2026-08-15_raft-master-plan.md:8-9`).

**DIFFERENTIALLY EVIDENCED — the actual claim at this tip**, on three
artifacts:

1. **Single RawNode, end to end** — *"the machine executes etcd-io/raft's
   RawNode end to end — election, leadership, a committed proposal, five
   Ready rounds — and agrees with gc on the drive's whole observable
   summary"* (`docs/raft-w41-log.md:551-556`; both oracles → `111035`).
2. **n=3 twin, per-step S1–S3 + S4-as-stop-condition, over 9 hand
   schedules** — *"**Both oracles — RESULT: agreement on every
   schedule.** … Zero disagreements to diagnose"*
   (`docs/raft-w42-log.md:366-369`).
3. **Upstream datadriven traces replayed under both oracles** —
   *"**OK-TIER: 178/178 agree** … **MACHINE TIER: 27/27 — COMPLETE**"*,
   byte-for-byte (`docs/raft-w42-log.md:426-432`).

**DESIGNED, NOT BUILT: the ∀-choice-stream form.** The design has the
driver consuming events from the choice stream
(`docs/2026-08-20_machine-twin-harness-design.md:47-48`); what shipped
drives hand-written schedules — *"THE SCHEDULE IS THE INPUT: v1 drives
named, hand-written schedules … The ∀ch-quantified form … is the
membership lane's"* (`tools/raftsubject/twin-lib.go:6-12`).

> **This is the load-bearing scope fact on link 2: the ∀ch
> quantification the eventual theorem needs has never been exercised on
> the twin.** It is an owed corpus row (`docs/raft-w42-log.md:597`), and
> *"the draw plumbing is new work"*.

#### Evidence artifacts

**Tracked and re-derivable:**

| artifact | what | verified by |
|---|---|---|
| `docs/evidence/2026-08-21_w42-census/sweep-post-swap.txt` | post-swap census: 24 quarantined, **5 LIVE** + 2 LIVE imported stubs, **7 residual sinks** | `tools/raftsubject/sweep.py` — **re-derived byte-for-byte at this tip by `tools/reconcile-records --heavy` (§2, check C11)** |
| `docs/evidence/2026-08-21_w42-census/sweep-pre.txt` | pre-swap census: 14 quarantined, 0 LIVE, census closed | same |
| `docs/evidence/2026-08-21_w42-census/tracefamilies.txt` | 309 rendered-expectation blocks by renderer family, two anchoring rules | `tools/raftsubject/tracefamilies.py`, fails closed if the sums disagree |
| `raftsubject/` (~11k LOC), `raftharness/` | subject tree + the go-run executable spec | `tools/raftsubject/derive.py --check` |
| the raft-path corpus rows in `baselines/native-full.tsv` | fmt/sprintf-verbs (22), strings/builder-model (7), multipkg/wire-codec (5), sync/promoted-mutex (5), maps/named-nil-flows (5), binary/little-endian (4), fmt/errorf (4), … | `scripts/ci --diff` |

**NOT tracked — the biggest structural finding on this link.** Every
number in the DIFFERENTIALLY-EVIDENCED list above is backed by files
under `artifacts/w42/`, which `.gitignore:5` excludes and which do not
exist in a fresh worktree: the four twin oracle-agreement verdicts
(`twin-{single,elect,perturb,ticks}.txt`), the 178/178 and 27/27
verdicts (`tracereplay-*.txt`), every gate transcript (`ci-*.txt`), and
the codec-vs-real-protobuf discharge log. The lane fixed this class ONCE
for the census (audit B-F4 created `docs/evidence/…`, whose README says
*"A number nobody can re-derive from tracked material is not a
record."*) and **did not extend the fix to the twin verdicts or the gate
transcripts**. At this tip the agreement claims are prose plus a
gitignored file.

**One reproducible executed cross-check exists:** the twin determinism
digest `12fe50c5d949c4382ba44f2ad2060471`, reproduced 3× from tracked
sources and 3× from the auditor's copy (`docs/raft-w42-log.md:262-268`),
with the honest retraction of an earlier non-reproducible digest three
paragraphs below.

**No gate covers any of it.** `grep -rln 'raftsubject|raftharness'
scripts/ .github/` returns nothing (verified). `scripts/ci` never builds
the subject tree, never runs the twin, never runs the trace replay,
never runs `derive.py --check`. The log says so: *"Nothing here lands in
a gate today"* (`docs/raft-w42-log.md:645`). **The entire machine→twin
agreement result is outside the regression envelope**; only its frontend
prerequisites are gate-protected.

#### The harness scope statements (the fine print)

**Recorded WITH a formal re-envelope obligation — one, and only one:**

- **Ready-harvest atomicity.** No node is stepped/ticked/proposed-to
  between its own `Ready()` and `Advance(rd)`. *"the v1 twin models
  FEWER interleavings than upstream licenses. The bundling is ours"* —
  refuted against `rawnode.go:411` (`stepsOnAdvance`) and `doc.go:101-103`.
  Five-row obligation table at
  `docs/2026-08-20_machine-twin-harness-design.md:112-118`; discharge at
  W4.5; widening = an additive `harvest` event. Cost stated plainly:
  *"a theorem about the twin is, at v1, a theorem about a SUBSET of
  conforming drivers."* **This is constitution §2.2.2's [MIKE] question 4.**

**Recorded as scope, obligation NOT formalized** (no register row, no
owner beyond "W4.5"):

- **Reliable-first network** — drop/dup OFF, unbounded reorder and
  delay. *"This is a strictly weaker theorem than raft's design point
  and the statement's docstring must say so"* (`design:145-152`).
  Mechanism exists flag-gated; `dup` additionally blocks on
  `proto.Clone` (H-1/G-4).
- **Fairness not assumed** — an adversarial stream may starve a node
  forever; concretized by the `starve-node` schedule (S1–S3 hold,
  `complete=0` EXPECTED — conditioned safety made concrete).
- **The schedule, not the choice stream, is the input** — no
  re-envelope obligation row exists for this at all.
- **n=3 fixed** — every twin schedule is n=3 except `probeTwinSingle`.
- **`campaign` in v1; timeout-driven elections excluded** (JC-22), now
  measured not derived: twelve `go run` campaigns landed at eight
  distinct tick values inside [10,19]. *"the ×3 determinism digest holds
  only because no v1 schedule crosses this site."*
- **`PreVote=false`** where the go-run family sets true — recorded, open
  question.
- **No crash/restart, no compaction, no snapshots-in-Ready, no
  conf-change apply.**
- **Fuel and iteration bounds, all fail-closed**: harvest loop 64 rounds
  (JC-23), drains 10000 (JC-24), interpreter fuel 2e8 (2e10 for
  `probe_and_replicate`). One whole-battery run was *"killed rather than
  trusted at fuel 4e9"*.
- **Two latent replay-mirror divergences, recorded and NOT fixed**
  (`splitMsgs` local-message guard; deliver/drop ordering), argued
  unreachable **on the supported subset only** — *"re-owed the moment
  the subset grows"*. The mirror is strictly STRICTER than upstream, so
  its failure direction is false-red, never false-green.

**The subject-delta ledger D-1…D-12** (constitution §2.2.3's cited
ledger) — `raftpb` stripping and its 64 dropped doc comments (D-1), the
`plain_clone` generation (D-2), two `raftpb` overlays (D-3/D-4), the
no-op Logger overlay **RETIRED 2026-08-21** (D-5), import-path rewrites
(D-6), the verbatim root package (D-7), `node_decls.go` keeping 11 of
`node.go`'s declarations and dropping 26 so *"the subject loses the
`Node` API entirely"* (D-8), the four generated runtime stand-ins (D-9),
`state_trace.go` not vendored (D-10), **the `lockedRand.Intn` jitter
choice site (D-11)** — distribution differs, envelope `[0,n)` identical
— and **D-12**, three code lines in `raft/logger.go`, whose retirement
is blocked on the new ticket **H-20**.

#### The tier-strength bound

**Terminology collision — flag it for the audit.** Two unrelated things
carry this name.

**(a) `tier=slow` / certified-set rows** (`scripts/diff-coverage`;
design `docs/2026-08-04_membership-lane-design.md:331-411`). A certified
row asserts the enumerated distinct observations under declared
width/sites/work/backedge bounds with a mandatory `members=n` cardinality
pin; for `engine=dedup` rows the meaning is stronger — `∀ o, o ∈ S ↔
SlowObs resultLocs m₀ r₀ o`, discharged by `checkCertM_slowObs`
re-running the real `stepMulti` per edge, with axiom pins in
`proofs/Audit.lean`. The **cached** path does no enumeration at all:
fail-closed gates only (record exists, `wire.json` sha256 matches,
`# params:` matches, go-side samples and the four driver-coupling
streams are members of the RECORDED set, cardinality holds), reported as
`CERTIFIED-CACHED`. Its honest residual is in the design: *"the quick
path cannot see MACHINE-side envelope drift."* `--slow` re-enumerates and
compares set AND wire hash. Scale: **exactly one live `tier=slow` row**.
**Bearing on link 2: none** — no raft-derived row is `tier=slow`.

**(b) W4.2's "tier-strength bound"** — the falsifiability limit of the
trace instruments, and the sharpest self-limiting statement in the
records (`docs/raft-w42-log.md:491-520`):

> *"**The ok-tier is blind to delivery-order unfaithfulness.** … A
> mirror that delivered a node's messages in a different order from
> upstream's, or ran a deliver where upstream ran a drop, would still
> answer `ok` on every one of the 178 blocks. 178/178 is therefore a
> real result about command acceptance and *no* result about the network
> discipline underneath it."*
>
> *"**The machine/byte tier is oracle-SYMMETRIC.** … it is structurally
> incapable of noticing that `replayenv.go` disagrees with `rafttest`. A
> mirror bug is invariant under it."*
>
> *"the mirror's fidelity today rests on **code reading**, not on either
> green number"* — and the W4.3 rendered tier is *"the first tier that
> can FALSIFY the mirror"*.

#### Known bounds and residuals

- **W4.3's done criterion is never discharged clause-by-clause** the way
  W4.1's five clauses were; it is satisfied in substance by
  `elect-propose-commit` but never asserted against.
- **W4.4(b) shortfall**: design predicted the 249 `ok`-expecting blocks
  asserted directly; measured 178/178 — those *inside supported
  prefixes*. The 71-block shortfall is nowhere framed as a criterion miss.
- **W4.5 entirely undone** — three named obligations: the harvest
  re-envelope, the jitter RANGE latitude entry, the §6 shared-nothing
  footprint run.
- **The §6 shared-nothing footprint check is NOT mechanized**, though
  the design says *"That side condition must be MECHANIZED, not
  asserted"*. Its five checklist items are argued in prose only.
  **Without it the sequential→concurrent reduction — the twin's entire
  claim to be about the concurrent system — is unsupported.**
- **Envelope entries owed and not filed**: the jitter range has NO entry
  in the latitude inventory; the harvest narrowing has NO row in the
  simplifying-assumptions register; master-plan C-B's "latitude entries
  at the standing dossier bar for every new choice site" is undischarged.
- **Census not closed**: 5 live quarantined declarations + 2 live
  imported stubs + 7 residual sinks, argued dead DYNAMICALLY with both
  halves probed — *"NOT closed the way W4.1's was, and honestly so"*.
- **Rendered tier: 0 of 309 render today**, with nine named frontend/model
  gaps; and the 58 pure-log-line blocks cannot be reproduced by the
  twin's installed logger by design (a recording logger is shared mutable
  state unless per-node — re-opening the §6 check).
- **Six owed corpus rows, none landed**, so nothing on this link is in
  the baseline and nothing is regression-protected.
- **Performance is the practical bound**: twin elect/perturb ~20–24 min
  each; `probe_and_replicate` the better part of an hour, twice killed
  by background-task lifetime before a detached rerun completed.
- **BUG-061 is an unexercised residual here, not a refuted one.** The
  pruning rule under-approximates `staticinit`; the raft subject tree is
  multi-package with composite-literal package-level vars — exactly the
  `structlit`/`addrglobal`/`arraylit` flavors among the 11 of 26
  residual. Byte-for-byte twin agreement did not surface it.
- **BUG-002's disposition is owed in the statement's docstring**
  (master plan C-D) before the concurrent twin. Undone.
- Process residuals recorded honestly: W4.1 item 5 landed on a RED gate,
  disclosed as a deviation (B-9); W4.2 item 1 has no saved gate transcript
  (B-F7).

---

### §1.3 LINK 3 — kit → statements (the statement TCB)

#### The claim

> **"top-level theorem statements must be SEMANTICALLY INTERPRETABLE
> without Iris — if Iris were deleted from the build, the statement must
> still elaborate and denote the same proposition in base definitions."**
> … *"This is stronger than human understandability and it is FORMAL:
> the transitive DEFINITIONAL CLOSURE of the statement … must be
> disjoint from Iris"*
> — `docs/2026-08-01_tcb-and-layering-doctrine.md:10-23`

Extended 2026-08-03 (the Prop-level relation `Step`/`Steps` joins Iris
outside the TCB) and again by the WP arc 2026-08-18 (the whole
`GoLean.Sym` namespace is a third refusal class,
`proofs/Audit.lean:212-222`). The kit's own side:

> *"the kit … is **untrusted method**: everything here is proof-side,
> and **no kit name may appear in a headline statement's closure**"*
> — `docs/kit-guide.md:7-10`

**In the TCB:** the `GoLean/` core (32,702 lines, of which
`GoLean/GoCore/` is 29,275), `proofs/GoLeanProofs/Surface.lean` (723 —
the deep-embedded Iris-free separation logic), the `Specs/*` statement
modules (~3,000), and `Examples/Targets.lean` + 7 designated
`*Program.lean` pins (~4,100). **≈40.5k in; ≈160k of `proofs/` out.**

**Excluded by proof or gate:** Iris entirely; the whole relation family
(`Step`/`Steps`/`StepE`/`StepM`/`StepMFine`/`StepsM`/`StepsMFine`/
`StepEC`/`GoPrimStepC`); `GoLean.Sym.*`; every kit module; `go_walk`;
the Laws/Lifting/Ghost tower.

**What the claim explicitly does NOT cover** — and this belongs in the
audit's opening frame: *"The frontend is trust surface too … nothing
here verifies that translation … That is validation, not proof, and it
is the honest status of every claim below"*
(`docs/verified-examples.md:61-68`).

#### Evidence artifacts, and which half is mechanized

| artifact | enforcer | mechanized? |
|---|---|---|
| **Exhaustive axiom sweep** — every constant in any `GoLean*`-rooted module, by module of origin (`proofs/Audit.lean:83-111`) | `#eval` throws at elaboration, under `scripts/ci` | **YES — exhaustive by construction, not a hand list** |
| **Statement-TCB walker** (the deletion test), `proofs/Audit.lean:183-510`; fail-closed on missing name, non-theorem, unresolvable constant, exhausted 2M budget; the `ConstantInfo` match is exhaustive with no wildcard | same `#eval` | **YES**, over the 56 designated names |
| **The designated list**, `proofs/Audit.lean:261-396` | walked by the above | membership YES; **no gate says which theorems MUST be on it** |
| **Axiom pins** — 636 `#guard_msgs in #print axioms` across `proofs/` (245 in `Audit/Kit.lean`, 162 in `Audit.lean`, the rest in 24 per-example shards); permitted set `{propext, Classical.choice, Quot.sound}` | build error on drift | **YES** |
| **Witness references** — 300 `example := @…` lines | deleting a witness or law breaks the build | **PARTIAL — deletion gated, EXISTENCE not** |
| Proofs-file audit coverage; surface purity; statement-TCB closure gate; import-direction lint ("Exceptions: NONE"); meta-hatch allowlist (`EntryEq.lean` only) | `scripts/ci` | **YES**, all fail-closed |
| **Comparator judge** — independent kernel replay of Challenge/Solution | `scripts/comparator-judge` | **NO — manual, landmark cadence, explicitly never in `scripts/ci`** |
| "Every headline ships a first-order readout" | — | **NO** (true in fact for all 56; unmechanized) |
| "No kit name in a headline closure" | — | **NO** (only Iris / the relation / `GoLean.Sym` are refusal classes) |
| Deletion tests for the 18 undesignated gallery entries | run **by hand**, recorded per unit | **NO** |

#### The designation list state

**56 names**, `proofs/Audit.lean:261-396` (verified by count at this
tip). Composition: 34 quorum/golden/recover surface theorems, 5
fork-join stream theorems, 5 concurrent (`…C`) forms, 2 imported-goose
nil, 2 imported-goose Actris channel, 8 verified-examples gallery
headlines (fib, gcd, reverse, minmax, binsearch, isort, wordcount).

**Last changed `e4202039` (2026-08-14)**, "Designate the
verified-examples gallery headlines (48 → 56)"; the only later touch is
comment-only. Growth: 23 → 25 → 33 → 38 → 43 → 44 → 48 → 56.

**The walker runs in `scripts/ci`** — `scripts/ci` builds `proofs`,
whose `defaultTargets` include `Audit`, and the two `#eval`s execute at
elaboration. Success prints per-theorem closure sizes, so growth is
visible.

**Lockstep holds and is checked — but only outside `ci`.**
`proofs/judge-config.json` has exactly 56 `Judge.*` names;
`proofs/Challenge.lean` has 56 sorry-bodied theorems; `proofs/Solution.lean`
has 56. `scripts/comparator-judge` diffs the designated list against
judge-config by short name and refuses on collision — but that check
runs only inside the comparator, never in `scripts/ci`, and
`Challenge`/`Solution` are **not default Lake targets**, so `scripts/ci`
never builds them at all.

#### The pins census

There is **no separate census document — the census IS code**: 636
`#guard_msgs` pins plus the exhaustive sweep that needs no list.

**Claimed tips vs reality (re-verified at this tip):**

| claim | where | status |
|---|---|---|
| Kit pins "240 … at `8b36bf15`, at `69ef4bda` **and at HEAD**" | `docs/wp-arc-log/INDEX.md:234` | **STALE.** Re-run of the INDEX's own command at `521f5b57` → **245**. The commit-qualified halves are right; the bare "at HEAD" is exactly the tip-relative cite the same file's conventions block forbids. |
| Comparator landmark "PASS, 56/56 in 308 s @ `e42020397648`" | `docs/2026-08-02_comparator-judge-sprint.md:373-391` | accurate as recorded; that commit is **371 commits behind HEAD** |
| "the differential (zero drift on the full corpus — 872 cases as of 2026-07-31)" | `proofs/Audit.lean:1978-1980` | date-qualified so honest, but **2.7× stale** against 2343 today — a recurrence of the exact drift the sentence itself narrates |
| dot-in-path judge bug "Owed to the next arc that touches the judge wrapper" | sprint doc `:408-415` | **already FIXED** at `scripts/comparator-judge:167-170`; the owed-item text was never retired |

**The material finding on the census.** The last INDEPENDENT
certification is over a tree whose statement TCB has since MOVED.
`e42020397648..HEAD` adds three `Expr` constructors to
`GoLean/GoCore/Syntax.lean` (`addrOfDeref`, `runesFromString`,
`stringFromRuneSlice`), changes `GoLean/GoCore/Value.lean`, and changes
`proofs/GoLeanProofs/Examples/Targets.lean` — **inside Challenge's
trusted closure**. `Expr` is reached by every designated statement's
closure. The CLAUDE.md landmark trigger is scoped to *designated-set or
statement* changes, so a GoCore change that alters every designated
statement's definitional closure does not fire it, and `scripts/ci`
does not build Challenge/Solution either. **This is the single strongest
candidate for a pre-launch action item on link 3: re-run
`scripts/comparator-judge` at the settled tip.**

#### Witnesses

**16 named witness theorems** (`wp_assign_lit`, `wp_index_get_witness`,
`wp_len_slice_witness`, `wp_swap_witness`, `wp_call_value_start_witness`,
five `wp_panic_*`/`wp_breakable_*` witnesses, three `wp_map_iter_*`
witnesses including the defined-key instance, `wpC_spawn_noop_witness`,
`wpD_spawn_noop_witness`, `raft_linearizable_conclusion_witness`), plus
a set of unnamed-suffix witnesses referenced from the gate.

**Correctly marked scaffold:** `NPDRFReduction`
(`GoLean/GoCore/NPDRF.lean:41-48` — *"DRAFT FORM, REFUTABLE AS WRITTEN …
Nothing may cite this"*); the `GoSpecC` residual
(`Surface.lean:568-600`); the deliberately law-less `typeAssert` twin
(`Laws/StmtOps.lean:866-869` — *"it lands with its first consumer"*, the
rule working as designed); two tombstones recording deletion under the
same rule; the Gobra `GoFuncSpec` joint (`TODO.md:728-731`).

**Two live violations — neither witnessed nor marked scaffold:**

1. **`wp_map_iter_done_nil`** (`proofs/GoLeanProofs/Laws/Range.lean:93`)
   — carries `@[go_walk_law]`, so it is user-facing automation; zero
   applications anywhere; **not named in `proofs/Audit.lean` at all**
   (verified: `grep -n wp_map_iter_done_nil proofs/Audit.lean` → no
   match), so not even the deletion tripwire sees it. Its docstring
   asserts applicability.
2. **`wp_map_range_enter_nil`** (`Laws/StmtOps.lean:208`) — cited at
   `proofs/Audit.lean:1069` as `example := @…wp_map_range_enter_nil`,
   but that names the **law**, not an instantiation; the witness the
   gate docstring then names discharges the **non-nil** form.

**Structural cause, and the reason this is a link-level finding rather
than two typos:** ~80 of the gate's 300 `example := @…` lines name a
LAW rather than an instantiation, so the law↔witness pairing is carried
**by docstring prose only**. And 60 of the 123 `theorem wp*` laws under
`Laws/**` are never named in `Audit.lean`, covered only by a blanket
sentence. **The rule is half-mechanized: deletion is gated, existence is
not.** `scripts/proof-lint` has zero witness content and is deliberately
report-only. `Audit.lean:935-936` concedes the failure mode itself —
`wp_breakable_done` *"had no witness at all"* and was found by a human
audit, not by the gate.

#### SlowObs and the certified-quotient bridge

**State: PROVED, sorry-free, axiom-pinned, in the default `lake build`.**
Not designed-only, not partial.

- `Obs` (`GoLean/GoCore/EnumSpec.lean:35-39`), `obsOf?` (`:45-54`, total
  six-arm projection; deadlock / fuel-out / stuck / unsupported all map
  to `none`, so a divergent branch observes nothing at any fuel), and

  ```lean
  def SlowObs (resultLocs : List Loc) (m₀ : MultiConfig) (r₀ : RaceState) (o : Obs) : Prop :=
    ∃ fuel ch, obsOf? resultLocs (execProgLoop fuel m₀ r₀ ch) = some o
  ```

- The bridge, `GoLean/GoCore/EnumDedupSound.lean:944-950`:

  ```lean
  theorem checkCert_slowObs … (hc : checkCert nodeEqb resultLocs m₀ r₀ cert = true) :
      ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs resultLocs m₀ r₀ o
  ```

  **Set EQUALITY, not one-sided**: soundness by witness replay,
  completeness by fuel induction over the certified graph. Instantiated
  as `checkCertM_slowObs` (`:999-1004`).

**Note the shape, because it is easy to over-read.** The theorem relates
a **certificate** to `SlowObs`; it does *not* relate the optimized
enumerator to a reference enumerator. The optimized engine
(`GoLean/EnumDedup.lean`) is untrusted and deletable by construction — a
bug there can only make the checker REFUSE. Separately, the old DFS
enumerator (`GoLean/CLI.lean:1239/:1291`, `partial def`s) has **zero
proof surface**, and its rows keep the older bounded-tree claim.

In the default build via `GoLean/GoCore.lean`; axiom-pinned at
`proofs/Audit.lean:619-624` — pins **added by the audit-fix round, not
the slice** (finding B-F1: *"the slice shipped its headline theorem with
no axiom pin at all, so a `sorry` reintroduced anywhere under it would
have been invisible to this gate"*).

**W3.2 status:** slice 0 DONE, slice 1 DONE (stages A–E), POR slice DONE
+ audit-fix round. **Slices 2, 3, 4, 5, 5b, 6 are DESIGNED-ONLY**; 6a
additionally HOLDS for Lean-SpecTec.

**Channel-logic park:** the charter on `main` is the pre-arc scoping
document and contains **no park record** — the park lives on the
unmerged `channel-logic-s4` branch. Resume condition: the machine
re-envelope phase, whose exit artifact §S6c *"states, checkably, what the
resume gets"* — **§S6c is not yet built**, so the condition is unmet.

#### Escape-hatch census (`.lake` excluded, hand-checked)

| token | real uses |
|---|---|
| `sorry` | **56**, all in `proofs/Challenge.lean` — by design; sorry-bodied challenge statements ARE the artifact |
| `sorryAx` / `admit` / `native_decide` / `ofReduceBool` | **0** |
| `axiom <name>` | **0** |
| `unsafe` / `opaque` / `@[implemented_by]` | **5**, all in `proofs/GoLeanProofs/EntryEq.lean` — exactly the one allowlist entry |
| `partial def` | **21** — `NativeToIR` 10, `CLI` 7, `Tactics/GoWalk` 2, `EnumDedup` 1; **0 in `GoLean/GoCore/`**, so CLAUDE.md's claim holds |

#### Known bounds and residuals

- **18 of 26 gallery headlines are UNDESIGNATED** — deletion tests run
  by hand, axioms pinned in-build, but never walked by the gate and
  never comparator-replayed. Designation is Mike's act.
- **OQ5 — the one open W3.2 question with no default**: what `nonterm=`
  means under `engine=dedup`. *"This one changes what a green row
  asserts."*
- **BUG-065** open, narrowed to one row (`goroutines/worker-pool/sum`,
  >9.5M nodes, no closure), pinned FAIL; fix routes through slice 5.
- **`spec-parity-s2` parked RED** — 16 open proof errors on a branch.
- Driver-level PANIC assembly QUEUED, not claimed.
- Kit residuals: key-generic maps parked with three pullers; the
  element-kind-generic `SliceMem`; choice-dependent layout; struct-cell
  generalization (*"expected to matter more than key-genericity at the
  raft target"*); §5's measured REVERSAL is a recorded open question.
- Doctrine requirements not mechanized: the readout-corollary mandate;
  "no kit name in a headline closure"; deletion tests for undesignated
  theorems; Challenge/Solution statement-identity against the live
  theorems.
- **F-5 (new, not on any findings list):**
  `GoLean/GoCore/EnumDedupCheck.lean:19-27` describes the certified
  fragment as N-OBL + N-L4 only, **omitting N-APP** — which `innerVecs`
  implements and `EnumDedupSound.lean:125-258` proves. A trust-surface
  docstring under-describing the fragment it certifies.
- **F-7 (new):** `SlowObs`/`checkCertM_slowObs` — the strongest new claim
  on the branch, and what every `engine=dedup` certified record MEANS —
  is axiom-pinned but **not designated**, hence never comparator-replayed
  and never walked by the statement-TCB gate. It lives in
  `GoLean/GoCore/` (TCB territory) rather than in the designated
  statement layer. Given the constitution's ideology (§3: *"the
  observation notion is load-bearing"*), this is the artifact the
  ideology most points at, and it is the one outside the designation
  discipline.
- **F-10 (recorded in situ, worth carrying):** the certified record's
  warning that `width=`/`sites=` do not bound the claim under
  `engine=dedup` is written as `# params-note`, which the record
  parser's `# params:` extraction does not match — i.e. deliberately
  parser-invisible. Confirm that was intended.

---

### §1.4 LINK 4 — the instruments (do the gates compose honestly end-to-end?)

#### The claim

`scripts/ci` is the one-command gate. It re-execs through `scripts/capped`
unless `GOLEAN_CAPPED` is `verified` or `none`; it **exits 2 on any
unrecognized flag**; it runs EVERY step even when one fails, accumulates
into a results array, and exits 1 if any step failed. Its claim is not
"the code is correct" — it is: *nothing regressed against the recorded
failing set, nothing escaped the axiom/witness discipline, and nothing
silently skipped.*

#### The gate inventory — 27 steps, what each proves, what each cannot see

Sources: each gate's own header comments, plus the audit history.

| # | step | proves | structurally cannot see |
|---|---|---|---|
| 0 | build parallelism | nothing — self-declared *"A PERFORMANCE KNOB, NOT A CORRECTNESS GATE"* | — |
| 1 | escape-hatch preflight | no `sorry`/`admit`/`native_decide`/`ofReduceBool`/`axiom` in `GoLean/`+`proofs/` outside `Challenge.lean` | its own header defers to step 13 as authoritative. **Block comments are not stripped** — any line containing `/-` is dropped (§ below). **Zero enumerated files ⇒ silent PASS** |
| 2 | meta-layer hatches | no new `unsafe`/`opaque`/`@[implemented_by]` outside `EntryEq.lean` | its own header: this class is *"invisible to `#print axioms` because the divergence is in the evaluator, not the proof term"* — so this scan is the ONLY check for it |
| 3 | proofs-file audit coverage | every `proofs/**/*.lean` is in the audited closure or on the standalone allowlist | cannot see the CONTENT of an allowlisted file — and `Solution.lean` is allowlisted |
| 4 | fidelity-bug index (`check-bugs.sh`) | BUGS ↔ baseline consistency + the per-class and SET ratchets | its stage filter is a fixed list; `go-run`-stage reds are invisible (recorded, accepted). The list has been reopened lane by lane — membership, then confluent/racy, then nondet |
| 5 | feature coverage | no dead canonical tag; no husk case-directory | **the all-failing WARN is not fatal and `ci` never passes `--strict`** — live: 4 tags (`atomics, cond, goexit, real`) have cases and ZERO passing, and the banner reads `ok (no dead tags)` |
| 6 | spec-anchor citations | every `spec#`/`mem#` citation resolves at the pin, checkout rev-verified and diff-clean; fails closed on zero citations | its own header: *"checks RESOLUTION only — it cannot see a resolving anchor attached to a misquoted or stale clause text"*; the audit that found five such quotes proves the class is real |
| 7 | lane-validation (fast) | 33 bad-shape fixtures rejected; G1–G4 infra-death gates | fixture-based: it proves the gates reject the shapes SOMEONE WROTE DOWN |
| 8 | imported-goose verbatim | above-marker bytes == pinned upstream; import grants both directions | **silent pass if the lane directory is absent** — the one `if [ -d ]` skip in the gate |
| 9 | surface purity | 30 listed files' imports match anchored allowlists; `GoLean/` has no Iris ⇒ the chain closes; a listed file that does not exist FAILS | **the list is hand-maintained with no completeness mechanism** — the exact class that reopened for ~10 days in 2026-08. Origin: the 2026-07-23 rename hole, *"invisible to eleven green steps"* |
| 10 | statement-TCB closure | no designated theorem is DECLARED in Challenge's closure; fails closed on an empty designated-name list | matches `theorem` only. **Vacuous if `Challenge.lean` yields no imports** (§ below) |
| 11 | import-direction lint | three clauses, two fail-closed on missing dirs/zero files | clause (c) is **DIRECT-import only** — *"a `GoLean/*.lean` intermediary … would be missed. Recorded, not fixed"*. Clause (a) has no zero-file guard |
| 12 | core build | compiles, and emits no `warning: GoLean/` line (such warnings corrupt the JSON observation channel) | a green build is not evidence of correctness; `proofs/` warnings pass |
| 13 | **proofs + the in-build `Audit` gate** | the authority: an exhaustive module-of-origin `collectAxioms` sweep that throws on any disallowed axiom, the curated pins, the statement-TCB CONSTANT walk (exhaustive over `ConstantInfo`, no wildcard), witness references, and fail-closed existence anchors so a rename fails the build | axiom-clean ≠ non-vacuous. Cannot see the meta layer. **Cannot see a headline theorem never ADDED to the list** — precisely W3.2's B-F1: `checkCertM_slowObs` had no pin, so *"a `sorry` reintroduced anywhere beneath it would have passed every green step"* |
| 14–15 | proof-cost trend, storm lint | **nothing** — report-only by explicit policy (*"DO NOT HARDEN"*); `proof-lint` ends in an unconditional `exit 0` | a crash inside them is reported as a note. Do not count them as gates |
| 16 | verdi compat | the port builds with the ENFORCING `AxCheck`; the fixture byte-matches | its own header: *"The Rocq extraction oracle … NEVER runs in ci"* |
| 17 | import-goose self-test | the importer's reject-shape and tamper fixtures behave | fixture-based |
| 18 | golden lowering | for 28 pinned programs, BOTH links (fresh frontend→decode == `.repr`, and the checked-in term prints the same), plus the E7 deviation-observation pin; both sides built first so a stale `.olean` cannot mask drift | **no registry-completeness cross-check** — `PINS` is a hand-maintained array; a new golden pair not added to it is silently unguarded (currently complete, but there is no MECHANISM — unlike its own descendant, step 19) |
| 19 | imported-goose R2 pins | 11 pins, term == decoded(frontend(source)), **plus** a registry cross-check that the on-disk glob equals `PINS` exactly | scope stated in situ: a pin module outside that glob is not seen |
| 20 | frontend unit tests | the monomorphization identity layer — *"exercised by `go test`, not by the differential"* | only that package |
| 21 | eval tests | exit 0 and zero `not ok`/`fail` lines; now carries the W3.2 checker mutation-refusal suite + a positive control | a differently-shaped failure line relies on the exit code alone |
| 22 | **differential run** (`--diff`/`--slow`) | the run COMPLETED; exit ≥2 = infra, and results+meta are removed UP FRONT so a dead run leaves nothing judgeable | judges completion only. **`-race` is used only when `expected_status == race` or membership sampling asks — the strict and confluent lanes never build with it** (the confirmed BUG-045 fail-open) |
| 23 | lane-validation (go half) | F4/F6 and the slice-4 lane gates | fixture-based |
| 24 | negative corpus run | each compile-rejection case fails with the expected substring; zero cases ⇒ exit 2 | a reworded but equivalent gc message fails; a different-cause rejection with the same substring passes |
| 25 | negative baseline diff | the negative failing-set is identical; **no record ⇒ FAIL** unless the hatch | — |
| 26 | **differential baseline diff** | the heart: meta must exist, its `manifest_sha256` must match a regenerated manifest, staleness vs HEAD is surfaced, a partial run is a `note` NEVER a certification, and **no record at all is a FAIL** | its own header: *"corpus SOURCE bytes are not in the manifest, so an edited `main.go` is only re-validated by a fresh `--diff` run"*. Only `result`+`stage` is the signal — a refusal TEXT change is invisible |
| 27 | re-pin guards ×2 | every PASS→non-PASS flip a re-pin introduces is listed as a whole token on a `- Cases:` line in BUGS.md; a shallow clone without `HEAD~1` FAILS CLOSED; the awk comparison's own exit status is checked | CI audits only the tip (multi-commit pushes are covered pre-commit). **Cannot tell a RENAMED id from a REGRESSED one** — recorded, and it blocked a chartered rename rather than being laundered |

#### The gates outside `ci`

- **`scripts/comparator-judge`** — the independent kernel-replay judge:
  every theorem in `judge-config.json`, AS STATED IN `Challenge.lean`, is
  proven in `Solution.lean` using no axiom beyond the classical trio,
  re-checked by exporting both environments and replaying the Solution
  into the kernel — independent of our proof scripts, Audit pins and Lake
  state. Defaults to a FRESH CLONE of committed HEAD; `--in-place` is
  verdict-labelled *"iteration-grade, NOT authoritative"*. It also
  verifies the trust tools are pristine, pins the permitted axioms in the
  SCRIPT rather than just reading the config, checks designated-list
  lockstep + short-name collisions, and fails on unknown roots in its
  Iris-freedom walk. **Landmark cadence, human-triggered.**
- **The `--slow` tier** — full re-certification of `tier=slow` rows
  against the tracked certified set at the current wire sha and params.
  Nightly cron; `workflow_dispatch` defaults to it. **It currently
  re-certifies ONE corpus case.**
- **`compat/verdi/extraction/`** (the Rocq oracle), `comparator-setup`,
  `setup-deps`, `coverage report --full`, `proof-costs` (record mode) —
  all human-triggered.
- **The GitHub `gate` workflow** — push/PR runs the FAST gate with
  `GOLEAN_ALLOW_NO_DIFF=1`; schedule/dispatch runs the full gate. Both
  wrapped in a SYSTEM-scope cgroup via passwordless sudo, with the cap
  PROVEN by `capped`'s readback rather than asserted. Go pinned to
  exactly `1.26.5`.

#### The escape hatches

Every one is explicit, named in the failure message that prompts it, and
leaves a visible artifact: `GOLEAN_ALLOW_NO_DIFF` (degrades both
baseline-diff steps to a reported `note`), `GOLEAN_MEM_MAX=none`
(unconditional stderr WARNING), `GOLEAN_CAPPED=none` (warns on EVERY
invocation — the direct fix for a regression where the sentinel went
silent forever), `GOLEAN_CAPPED=<other>` (untrusted; must pass the
`memory.max` readback or exit 3), `GOLEAN_SLOW` (an INVERSE hatch — it
strengthens), the five timeout variables (each must match
`^[1-9][0-9]*$` or the run exits 2 — they were previously silently
disableable), the coverage-artifact redirects, and `--in-place`.

**There is no hatch to skip an individual `ci` step, and none to
downgrade `--diff` to fast. A typo'd flag exits 2.** This is a genuinely
strong result and the audit should record it as one.

#### Gate-honesty history — the register the repo keeps on itself

Green-while-broken, counted and dated: the purity-scan rename hole,
*"invisible to eleven green steps"* (CLOSED — a missing scan target now
FAILS); statement-bearing modules Iris-free-by-luck but ungated, found
~10 days after the hardening whose comment warns of exactly that class
(CLOSED); `comparator-judge` unable to run from any path containing a
dot — so from any lane worktree — *"latent-since-2026-08-02 and
invisible until the first landmark run from a worktree"*, ~13 days
(CLOSED 2026-08-15); the CI cache frozen at one entry for ~24 days;
**the E6 receive-bearing-`len` guard failing open**, which survived a
five-reviewer post-autonomy audit and was found only in fix round #2,
*after* the trip report had written "no gate was found failing open"
(CLOSED + 12 corpus rows); the `-race` fail-open (BUG-045), under which
**three shipped subjects passed the STRONGEST lane green while being
TSan data races**; and "no recorded differential run" exiting PASS —
*"That happened twice today."*

**Grown twice** (the same hole reopened): the `| _ =>` classification
wildcard in the statement-TCB gate — *"a VERBATIM regression … the repo
has now grown this bug TWICE and the gate's comment says so"* (now
exhaustive; an unhandled kind is a compile error); and the husk gate's
string scan, whose own FIX had a fail-OPEN raw-string residual.

**A fix that opened a new hole**, four instances — most sharply
`GOLEAN_CAPPED=none`, which was *"a new, totally silent fail-open with
exactly the semantics of the hole it was fixing … Worse than the
original."*

**Verification-method holes** (not gates, but relied on as evidence): a
published "zero survivors" grep whose own pattern had a hole; an 18%
undercount from a filename glob, in the self-favorable direction; a
float checker draft that silently PASSED on parse failure; and *"two
'green' checks were FALSE greens — emptied command output read as
success."*

**Recorded as NOT closed** — the standing residuals: the wire decoder
does not check unknown/extra keys AT ALL (fail-OPEN; `requireExactKeys`
is used 19× in `CLI.lean` and **zero times** in `NativeToIR.lean`, and
even the proposed fix cannot see three of the cases); covmap `status`
fails open on exit code; the engine-isolation scan is direct-import
only; the race detector is a fail-open under-approximation BY DESIGN
(`¬refusal ⇏ DRF`); corpus source bytes are not in the manifest; the
re-pin guard cannot distinguish a rename from a regression, and audits
only the tip in CI; `check-bugs --list` has no `go-run` stage; per-row
enumerator budgets do not compose with the job-level 120-minute timeout,
so a hung enumeration kills the step with nothing published; the CI cap
constant derives from an unmeasured cold-runner peak; judge binaries are
built artifacts outside the pristine check; **macros, notation and
attribute extensions are invisible to any name-level scan** — the build
is the only confirming check; and W4.1's DONE criterion was fail-open by
construction.

#### Composition risks — the class no single arc's audit can see

1. **`Solution.lean`: the preflight is its only per-commit check, and the
   preflight is blind on `/-` lines.** `ci` allowlists `Solution` out of
   the audited closure on the grounds that *"Solution's axiom discipline
   is checked by the judge itself … The escape-hatch preflight still
   scans `Solution.lean` text."* But the preflight drops any line
   containing `/-`, and the judge is landmark-cadence. So
   `def f := sorry /- WIP -/` is invisible to every per-commit gate.
   Each gate defers to the other ACROSS A CADENCE GAP. (Currently clean:
   `grep -c sorry proofs/Solution.lean` = 0.)
2. **The statement-TCB gate defers to the judge for closure integrity —
   but the judge fails closed where `ci` does not.** The judge refuses
   outright if zero imports parse from `Challenge.lean`; `ci` has no such
   guard, so an empty frontier yields PASS. Neither guards the SHAPE of
   Challenge itself per-commit.
3. **`scripts/ci --diff` writes metadata the rest of the toolchain reads
   as "not a full run".** It calls the differential with no manifest and
   no coverage env, so the published meta records `full_run unknown` and
   `latest-full.tsv` is **never written by the gate**. `ci` compensates
   by recomputing `ran >= total` itself — but `scripts/coverage report
   --full`, the only staleness check on `latest-full.tsv`, is therefore
   checking an artifact the canonical gate path never refreshes.
4. **The differential and the race detector each assume the other covers
   concurrency.** `-race` runs only for `expected_status == race` or
   membership sampling. BUG-045's fix moved three cases to the racy lane;
   it did NOT add `-race` to the strict/confluent lanes. **The strongest
   lane still cannot see a data race, and the racy lane only covers cases
   someone already suspected.**
5. **`check-imported-goose` deliberately runs no compiler, deferring to
   the differential — which the fast gate does not run.** Push/PR CI runs
   the fast gate with `GOLEAN_ALLOW_NO_DIFF=1`, and a local `scripts/ci`
   with no flag reads a possibly-stale record. The deferred-to check runs
   nightly, not per-commit.
6. **`check-golden` and `check-imported-pins` are the same mold with
   different completeness discipline.** The latter cross-checks its
   on-disk glob against `PINS` and fails on any difference, explicitly
   *"closing the total-non-registration hole"*. `check-golden` — which
   that very comment names as its mold — has no equivalent.
7. **`check-spec-anchors` trusts `setup-deps`'s table; the workflow
   clones by TAG.** A retag upstream would be caught by the fail-closed
   rev check, but the pin's identity is a tag in one place and a SHA in
   another, reconciled only at gate time.
8. **A broken `coverage-manifest` degrades the fast gate silently** —
   `total=0` skips both the attributability check and the
   full-certification branch, and the fast gate records a PARTIAL note
   rather than a FAIL. Under `--diff` it does fail.

#### Gates that do not run what their name suggests

**First, the strong result, checked exhaustively:** every gate step that
is supposed to fail DOES check its exit code. `set -o pipefail` is on and
is inherited by the `( cd proofs && lake build | tail -4 )` subshells, so
the `| tail` does not swallow a build failure. The differential and
negative steps use `${PIPESTATUS[0]}`. **There are no `|| true` on any
gate's own verdict** — all eleven in `ci` are on `grep`'s legitimate
no-match exit inside a capture. `set +e` appears once and is immediately
followed by an explicit fail-closed `rc > 1` check.

The defects are all one class — **empty input / silent skip**:

- **I-1 (verified live).** The escape-hatch preflight drops any line
  containing `/-`. Block comments are not stripped here (unlike the
  closure walks, which use `strip_lean_comments`), so the filter is a
  blunt "line mentions `/-` ⇒ ignore". Mitigated by the in-build Audit
  gate for everything in the closure — NOT mitigated for `Solution.lean`
  or `SliceSpike.lean`.
- **I-2 (verified live at this tip).** `find GoLean proofs … -print0 |
  xargs -0 grep …` on missing directories exits **123 with empty
  stdout**; the step tests only `[ -n "$hatch" ]`, so it prints "none
  found" and calls `ok`. **If `GoLean/` or `proofs/` were renamed, both
  hatch scans would go green.** Contrast the Tactics clause 40 lines
  later, hardened for exactly this: *"a missing directory or zero
  enumerated .lean files FAILS the lint."* Two scans in the same file
  use opposite conventions.
- **I-3 (verified by reading, at `scripts/ci:545-560`).** The
  statement-TCB closure gate is **vacuous if `Challenge.lean` yields no
  imports**: `lean_imports` on a missing file returns rc=0 and empty
  output, the `while` never runs, the `for` iterates zero times, and the
  step reports ok. The sibling guard exists two lines above for the
  designated NAMES (*"failing closed"*) and in the judge — but not here.
  Rename `Challenge.lean` and step 9 catches it; comment out its imports
  and nothing does.
- **I-4.** Two more zero-iteration `while read` loops over `find` (the
  proofs-file coverage walk and one import-direction clause), same class,
  lower severity because sibling clauses in the same step fail closed.
- **I-5.** `grep -rEq "…Iris" GoLean/` returns 2 on a missing directory,
  which `if` reads as "no Iris found" — so the chain-closing arm of
  surface purity goes green if `GoLean/` is absent. A partial hole in a
  partially-hardened step.
- **I-6 (verified live).** `check-coverage`'s all-failing WARN is
  computed, is non-fatal because `ci` never passes `--strict`, and is
  then truncated out of view by `tail -2`. Live: **4 canonical tags have
  cases and ZERO passing — `atomics, cond, goexit, real`** — while the
  operator's summary line reads `ok  feature-coverage (no dead tags)`.
  The step's name is honest; **the claim it is cited for — "green implies
  covered" — is weaker than it reads.** The same truncation pattern
  appears at three other steps.
- **I-7.** `check-imported-goose` skips silently on a missing lane
  directory. Documented as the pre-population state and cross-covered by
  the baseline diff (82 dropped ids would drift) — but as written,
  deleting the lane directory turns a verbatim-provenance gate green.
- **I-8 (legibility, no correctness impact).** The step banner reads
  "re-run FULL native differential corpus" while invoking
  `scripts/diff-smoke` — a 7-line passthrough, so it IS full and the name
  is a fossil; a reader auditing the trust chain's foundation sees
  "smoke". Two `#` lines sit INSIDE a quoted banner string and print as
  banner text. And `proof-costs`/`proof-lint` are invoked from steps
  named "trend" and "lint" and never block — deliberate, but worth
  stating so nobody counts them as gates.
- **I-9.** `baselines/certified/` has **no orphan check**:
  `diff-coverage` fails closed on a MISSING record, but nothing detects
  an orphan record for a row that no longer declares `tier=slow`.

---

### §1.5 LINK 5 — the records (the ledgers reconciled against each other)

#### The claim

Six records are supposed to compose into one accounting, each with a
distinct job and an explicit rule about what belongs where:

| record | its job | its stated rule |
|---|---|---|
| `docs/BUGS.md` | the **single canonical** fidelity-bug index | *"A construct we don't model yet is not a bug … tracked as coverage, not here."* Machine-cross-checked against the baseline. |
| `baselines/native-full.tsv` (+ `untriaged-{ids,count}`) | what the machine ACTUALLY does, per case | the tracked record; `artifacts/` is not the record |
| `docs/language-coverage-ledger.md` | **the repo's coverage claim**, against the pinned spec | every baseline red belongs to an FR row, a Q row, a (c) pin or an (a)-queued fix; §8's arithmetic closes |
| `docs/coverage-ledger.md` | the mutable per-area coverage accounting | high-level; representative cases, not a manifest |
| `docs/spec-divergence-ledger.md` | the sharp questions, minimal programs, per-implementation data | one entry per divergence, L-NNN, with a kind |
| `docs/spec-interpretations.md` | the **index** of adopted READINGS | *"Every row is BACKED by a ledger entry … A reading without a ledger entry does not belong here"* |
| `docs/2026-08-11_latitude-inventory.md` | the per-point census of where the machine CHOOSES | one row per point, with class, evidence, obligation, cost |

The composition claim, in one sentence: **a red in the baseline is
explained exactly once, by exactly one of these, and the explanation is
current.**

#### Evidence: what enforces it

- `scripts/check-bugs.sh`, inside `scripts/ci` — the only mechanized
  link. It enforces BUGS ↔ baseline in both directions plus the
  per-disposition ratchet and the SET ratchet (added because *"the count
  alone launders equal-sized swaps"*).
- **Nothing else.** The coverage ledgers, the divergence ledger, the
  interpretations index and the latitude inventory have **zero script
  references** — three appear in `scripts/` only inside comments.
- `tools/reconcile-records` (§2) is this dossier's contribution and is
  explicitly NOT a gate.

#### Known bounds and residuals

**The full reconciliation is §2.** In summary: the mechanized half is
green and exact — the baseline's id set is the corpus's, the untriaged
set is the unexplained-red set in both directions, every BUGS case
resolves, and the ledgers' id namespace has **zero dangling
cross-references**. The unmechanized half has **10 tool findings and 19
read-level discrepancies**, concentrated in three places: the language
ledger's closing arithmetic (computed over a superseded baseline, with a
"verified mechanically" claim whose mechanism no longer exists), the
latitude inventory's §10 self-counts and its §0 choice-site census
(which claims to mirror code it is two sites behind), and a scatter of
tip-relative or superseded numbers across the arc logs.

**The class-level reading, which matters more than any single finding:**
every discrepancy found is in a SUMMARY layer — a count, an
enumeration, a closing arithmetic, a "at HEAD" — and none is in a
worker-level claim. That is exactly maxim (i)'s prediction (*"summary
layers are where drift lives … restated, never recomputed"*), holding
for the fifth consecutive records audit. It argues for a specific
remedy rather than a specific fix: **the derivable summaries should be
derived**, not restated — which is what `tools/reconcile-records` does
for a subset and what nothing does for the rest.

---

### §1.6 LINK 6 — the campaign machinery

#### The claim

The constitution is meant to be the campaign's governing instrument:
ends fixed (§2), means delegated (§5), "no cheating" made mechanical
(§3), carried across months by INSTITUTIONS rather than a task list
(§4). The launch-gate bullet asks whether **this constitution is
operative, the continuity conventions are provisioned, and worker
briefs carry the honesty conventions.**

#### State at this tip — the answer is "not yet", in three specific ways

**1. The constitution is an unratified DRAFT, and it is lane-local.**
Its status line still reads *"DRAFT — awaiting Mike's ratification"*.
The `proof-constitution` branch has exactly three commits, all
2026-08-21: the draft, the launch gate, and the governing-ideology
paragraph. **The latter two are Mike-directed ADDITIONS, not
ratifications** — §4.5's amendment form (a dated in-file ruling block)
is used nowhere in the file. **All 8 §8 sign-off questions are open**
(base predicate; the T1–T4 ladder and which T3 invariants are headline;
the network envelope tier; the RawNode serialization narrowing; the
liveness tier; the milestone set; the supervision seam; ratification
itself), and 8 inline `[MIKE]` markers survive.

**Verified structural fact: the constitution branch is 48 commits
BEHIND `main`** (merge-base `4ef05649`; `git log --oneline
proof-constitution..main | wc -l` → 48; the reverse → 3). It was
drafted against a tree predating W3.2 slice 0, slice 1 stages A–E, the
whole POR slice, the holes arc, W4.2, W7 prep and the go1.26.5 CI pin.
Its closing line — *"Every provenance pointer above was resolved
against the tree at drafting time"* — is true of `4ef05649`, not of
`521f5b57`.

**And nothing on `main` references it.** `grep -rn constitution docs/
CLAUDE.md TODO.md` → **0 hits** (excluding this dossier). The campaign's
governing instrument is invisible from the tree it governs.

**2. The maxims' provenance resolves — but three of the branch-state
flags are inverted.** All 16 maxims (a)–(p) were resolved against this
tip; every cited file exists. Verdicts:

- **13 RESOLVED cleanly**, several verbatim — (b), (d), (e) (Mike's
  ruling *"any latitude in the Go spec should be supported"*, both
  narrowings struck by name), (f), (g), (h), (i), (j), (l), (m) (the
  literal `EXERCISE FLOOR SHORTFALL` verdict string is at
  `raftharness/scenarios.go:68`), (n) verbatim, (o) verbatim, (p).
- **(a) — minor mis-attribution.** The measured "~25% per successor"
  claim is verbatim in the trip report's lesson 4; but the FIRST cited
  file, `docs/2026-08-15_brick-wp-promotion-wave-mapping.md`, contains
  **no percentage figure at all**. It supports the practice, not the
  number.
- **(c) and the §2.1 POR-design citation — flagged branch-state, but
  they have LANDED.** `docs/2026-08-20_semantics-design-audit.md` and
  `docs/2026-08-21_w32-por-design.md` are both on `main` at this tip.
  The caveats are stale in the safe direction.
- **(k) — flagged as resolved, but the cited state does NOT exist at
  this tip.** `docs/2026-08-10_channel-logic-arc-charter.md` on `main`
  is 93 lines with **no park section**; the cited *"tail: ARC PARKED"*
  exists only on the `channel-logic` branch, where the same file is 311
  lines. The constitution flags (c) and POR as branch-state and does
  **not** flag this one — so the flags are inverted from reality in both
  directions. (The same unflagged cite appears at
  `docs/2026-08-20_w32-re-envelope-charter.md:106`, so the defect is
  inherited, not invented by the constitution.)

**3. The continuity conventions are about half provisioned.**

| §4.3 requirement | state |
|---|---|
| snapshot refs before risky git ops | ✅ **real and in daily use** — `git for-each-ref refs/snapshots/` → **25 refs**, most recent dated 2026-08-21 |
| per-goal log files | ✅ established pattern (`gallery-campaign-log/`, `wp-arc-log/`, the raft/w32/holes/bugfix logs) — but **no proof-campaign log file exists** |
| one writer per worktree | doctrine only; no mechanical fence |
| **module status blocks** | ❌ **not provisioned** — no template, no convention file; the phrase appears only in the trip report and CLAUDE.md prose |
| stashes with completion notes | practice only |
| checkpoints every ≤5 units, recomputed | practice only |
| successors re-verify predecessors' top claims | practice only (this dossier does it; nothing requires it) |
| summary layers carry a build/probe/SHA | practice — and §2 shows live counterexamples |
| **worker-brief templates carrying the honesty conventions** | ❌ **not provisioned** — no template anywhere in the tree; the conventions live only in CLAUDE.md's long-cycle section |
| the serialization resource identified up front | semantic core + `Corpus/` + `baselines/` exist; ❌ **the pinned statement file does not** (W6.3 unstarted, `scripts/check-raft-goal` absent) |
| cross-doc cites unit-anchored or commit-qualified | ⚠️ **16 dangling `docs/*.md` citations at this tip**, two of them live lane-only (`2026-08-16_symbolic-domain-design.md` → `wp-design`; `2026-08-11_npdrf-reduction.md` → `channel-logic-s4`) |

#### Known bounds and residuals

- **`docs/gocore-semantics-upgrade-handoff.md` is DEAD** — last touched
  2026-07-18 — while `CLAUDE.md` still mandates appending to it for
  multi-session efforts. Roughly 35 arcs since have used per-arc logs
  instead. This is a gate-honesty-class residual in the process contract
  itself.
- **`docs/roadmap.md` carries a STALE banner flagged 2026-07-19** — the
  Gobra framing is obsolete, the Iris "later phase" wrong, the coverage
  claims superseded; a "full rewrite tracked as a task" that was never
  done. It is a launch-visible document that misdescribes the project.
  Its Phase 6 (the user-facing Lean output surface) has no status line
  and no work anywhere.
- **Three colliding `H-<n>` registers** — the raft handoff (H-1…H-20),
  the hole census (H-a…H-f), and the W7 desugar inventory's Chapter H
  rows (H-1…H-6). "H-11" is ambiguous without naming a file. An auditor
  trip hazard worth fixing before eight reviewers read in parallel.
- **`TODO.md` carries at least three stale summary claims** — line 172
  still says "85 baseline fidelity failures not yet explained" (actual:
  15, in three dispositions); lines 112/187 still treat BUG-001 as open
  (fixed 2026-08-18); the Arc D header says IN PROGRESS while its body
  records the merge. Plus ~20 Gobra-era rows nothing marks as superseded.
- **`compat/gobra` is UNGATED** — zero references in `scripts/ci`; its
  ~70 `#guard`s and advisory `AxCheck` run only on a human build.
  `compat/verdi` IS gated.
- **A cgroup kill is SILENT** — `scripts/capped` execs, so it cannot
  observe an OOM exit 143.
- **`GOLEAN_ALLOW_NO_DIFF=1` is required in a fresh lane worktree** —
  this one has no `artifacts/coverage/`, so `coverage-baseline-diff`
  would fail by design. Correct behaviour; worth stating so the audit
  does not read a `note` as a weakened gate.

---

## §2 THE MECHANICAL PRE-RECONCILIATION

### The instrument

`tools/reconcile-records` — READ-ONLY, fixes nothing, writes nothing.
It is deliberately **not** in `scripts/`: this is an audit instrument,
not a gate, and the gate is not this dossier's to touch. Its exit code
is 0 whatever it finds (`--strict` flips that); `--json` emits the whole
derivation; `--heavy` additionally re-derives the census evidence.

Its scope is exactly the invariants that live only in PROSE. The
BUGS.md ↔ baseline invariants are already mechanized inside
`scripts/ci` by `scripts/check-bugs.sh`, and this tool runs that script
and reports its verdict rather than re-implementing it.

| check | what it reconciles |
|---|---|
| C1 | baseline shape: cases, PASS/FAIL by lane and stage |
| C2 | runs `scripts/check-bugs.sh` and reports its exit (the gate's own BUGS ↔ baseline invariant) |
| C3 | BUGS.md case ids exist in the baseline; **the baseline's id namespace == the corpus manifest's** (a drifted baseline is a record of a corpus that no longer exists) |
| C4 | the language-coverage ledger §8 closing arithmetic against the CURRENT baseline, and the red-bucket table's internal sum |
| C5 | every frontier-table (FR-n) case citation resolves, and every cited case is actually red |
| C6 | dangling cross-references across all of `docs/`: `BUG-n`, `L-nnn`, `I-n`, `FR-n`, `Q-NAME`, `L:<latitude row>` |
| C7 | every interpretations row is backed by an existing ledger entry; every ledger entry marked ADOPTED READING is indexed; the ledger's own entry self-count |
| C8 | tracked untriaged ids ⊆ baseline reds at a fidelity stage, both directions, recomputed independently of check-bugs |
| C9 | the certified record: its case exists and PASSes at `membership`; the wire schema has not moved since the certification date |
| C10 | the latitude inventory's §10 ENUMERATIONS against each row heading's own class tag |
| C11 | `--heavy`: the W4.2 census evidence re-derives from the tree |
| C12 | the choice-site census table against the `ChoiceSite` datatype it claims to mirror |
| C13 | every patch-level Go version named in `docs/` against the pin in `docs/spec-sources.md` |

**Anchor line at this tip:**

```
baseline    2343 cases  2199 PASS  144 FAIL
bugs        67 entries  8 open  59 fixed
untriaged   15 tracked  {coverage: 11, latitude: 4}  ceilings {coverage: 11, latitude: 4, wrong-answer: 0}
ledgers     15 L-entries  7 I-rows  15 FR-rows  10 Q-rows  39 latitude rows
```

### What PASSED — recorded, because a passing invariant is evidence too

- `scripts/check-bugs.sh` is **green**: 67 bugs, every pinned case behaves
  as claimed, backlog `coverage 11/11; latitude 4/4; wrong-answer 0/0`.
- **The baseline's id set is exactly the corpus manifest's** — 2343 both
  ways, zero stale rows and zero unrecorded cases.
- Every BUGS.md `Cases:` id exists in the baseline.
- The untriaged set is exactly the unexplained fidelity-red set, in both
  directions, with every disposition valid — recomputed independently.
- **Zero dangling cross-references** anywhere in `docs/` for `BUG-n`,
  `L-nnn`, `I-n`, `FR-n`, `Q-NAME` or `L:<row>`. The ledgers' id namespace
  is internally closed.
- All 7 interpretations rows are backed by an existing, distinct ledger
  entry; no ADOPTED-READING ledger entry is unindexed; the ledger's
  self-count of 15 is right.
- The certified record's case is `PASS/membership` and no commit has
  touched `tools/nativefrontend/wire.go` or `GoLean/NativeToIR.lean`
  since its certification date.
- **The W4.2 census evidence re-derives BYTE-FOR-BYTE at this tip**
  (`--heavy`, check C11). The one link-2 artifact that was tracked
  because an audit demanded it is also the one that reproduces.
- The frontier table's per-row red counts sum to 84, matching §8's
  frontier bucket exactly — though only 73 of the 84 are re-derivable
  from the rows' own citations (see R-4/R-4b).

### The findings — 10 from the tool

Severity is a GUESS, offered to help the audit triage, not a ruling.

| # | check | sev | finding |
|---|---|---|---|
| **R-1** | C12 | **HIGH** | The latitude inventory's choice-site census table has **7 rows**; the `ChoiceSite` datatype it declares itself a mirror of has **9 constructors** (`appendSpill, backEdge, l1Sched, l2Arrival, l2Entry, l4Waiter, l5ExitWindow, mapIter, postOp`). `postOp` (W3.2 stage C) and `backEdge` (stage D) are missing. The inventory says *"a new site requires a constructor (exhaustiveness-checked) and this table below is a reader's mirror, no longer a hand-synced record"* — the exhaustiveness check is real, but it protects the CODE, not the table, and the table is what a reader consults. The same 7-item list is repeated in `docs/2026-08-04_nondeterminism-doctrine.md`. **Why this is the top finding: the choice-site census is the enumeration of where the machine's nondeterminism enters. A reader's census that is two sites short is a census of a different machine.** |
| **R-2** | C4 | **HIGH** | `docs/language-coverage-ledger.md` §8's closing arithmetic is computed over a superseded baseline: §8 says 2219 cases / 2090 PASS / **129 FAIL** (recorded 2026-08-19); the tracked baseline is **2343 / 2199 / 144** (recorded 2026-08-21). The file is dated-honest about its vintage — but it also declares itself *"the repo's coverage claim"*, and its headline invariant is *"the 129 baseline reds, **every one on a named row** (verified mechanically at the re-pin — zero unmapped, zero double-mapped)"*. |
| **R-3** | C4 | **HIGH** | The direct consequence: §8's red buckets account for 129 reds; the baseline has 144. **15 reds are not on a named row at this tip.** The claim "zero unmapped" is not re-derivable. Compounding it: the phrase "verified mechanically" names no script, and no such script exists in `scripts/` — the verification was performed but its mechanism was not retained, so nothing re-checks the mapping when the baseline moves. |
| **R-4** | C5 | **HIGH** | **Two frontier rows have NO red left — every case they cite now PASSes.** FR-5 (sync ops in promoted/embedded/expression positions) claims 2 reds, `sync/escapes/{defer-embedded,promoted}` — both `PASS/-`. FR-8 (defined-type-aware typed nil, BUG-014) claims 2 reds, `maps/nil-literal-values/defined-{map,slice}-element` — both `PASS/-`, as are all 8 rows of that family. §4 declares itself *"the authority for every red case in the baseline"*, so **the features appear to have landed without their rows retiring** — a finding in the GOOD direction that nothing surfaced. FR-5 is queue position 5 and is marked **raft-path TOP**; FR-8 is queue position 8. Both queue slots may be spurious. (BUG-014 was closed at `f981f7cd`, which is consistent.) 4 of the 84 reds §8 attributes to the frontier do not exist. |
| **R-4b** | C5 | MEDIUM | Three further rows claim a red count not mechanically re-derivable from their citations: FR-9 claims 1 but cites 2 reds (the `atomic-frontier/value` "D5-stub adjacency" the count deliberately excludes), FR-13 claims 8 but cites one resolvable id plus the prose family "F3 family 7", FR-14 claims 7 but cites 6 plus an ellipsis glob. These are citation SHORTHAND, not obviously drift — but they are why the 84 is only 73-re-derivable, and each needs a read. Precisely: claimed 84, mechanically resolved 73, gap 11 = FR-5 2 + FR-8 2 + FR-13 7 + FR-14 1 − FR-9 1. |
| **R-5** | C10 | MEDIUM | The latitude inventory §10's `(b) PINNED` enumeration omits **C9** (global deadlock detection), whose own heading reads "(b) PINNED to gc's runtime detector". §10 says "structural: none remaining" for the C-series, which is true of C2/C3 (both re-enveloped) but not of C9. So the stated "15 entries" is not a count of the rows: heading-derived is 17. |
| **R-6** | C13 | MEDIUM | **64 sites across 5 doc files name a patch-level Go version other than the pin** (`go1.26.5` / `go1.25.13` per `docs/spec-sources.md`). Concentrated in `docs/2026-08-20_go-scheduling-semantics-dossier.md` (56 sites, all `go1.26.7`) and `docs/coverage-ledger.md` (3 sites, `Go 1.26.4`). The dossier's are probe records on a NEWER toolchain than the pin — legitimate as archaeology, but the whole point of the pin is that the spec text and the thing that produced the numbers moved together, and a scheduling dossier whose probes ran off-pin is exactly the case where that matters. The coverage-ledger's are a stale toolchain claim. Each site needs a read; none should stay unlabelled. |
| **R-7** | C10 | LOW | §10's `(b)` enumeration names **C2 and C3**, both of which now carry `(a) ENVELOPED` headings (re-enveloped at W3.2 stages C and D). The parenthetical prose says so; the list was not re-derived. |
| **R-8** | C10 | LOW | §10's `(b-n)` enumeration names **E9** (heading now `(a)`, re-enveloped 2026-08-19) and **R13** (heading carries no class tag). |
| **R-9** | C10 | LOW | Three latitude rows carry **no class tag in the heading at all** — C10, R7, R13. Their class is readable only from the body, which defeats the heading convention every other row follows and is what made R-5/R-7/R-8 possible. |

### Read-level discrepancies the tool cannot mechanize — 19 more

Surfaced by the record surveys; each is dossier material on the same
footing, and each is left uncorrected.

| # | where | finding |
|---|---|---|
| D-1 | latitude inventory §10 vs §5 | §10 says "REFUSED standing in for latitude: **9**"; §5 enumerates exactly **six** (R6, E6, select-with-select, racy programs, uintptr observations, `go` during `$pkginit`). |
| D-2 | doctrine vs inventory §8 | **The simplifying-assumptions register has colliding numbers.** The doctrine's register now runs 1–7 (#6 allocation addressing, #7 unbounded memory); the inventory's §8 extension still says "numbering continues the doctrine draft's 1–5" and starts its own #6 (int/uint width) and #7 (library-doc-silent behaviors). So "register #6" and "register #7" each name **two different entries**, and `docs/2026-08-04_nondeterminism-doctrine.md` cites one of them. |
| D-3 | language ledger §8 vs §6 | §8 says "Design-question mass: **9 questions**, 21 reds"; §6 has **10** Q rows. (Q-ATOMICITY carries 0 reds and is presumably the omitted one, but the sentence contradicts the table.) |
| D-4 | `docs/coverage-ledger.md` | cites "the installed **Go 1.26.4** toolchain" twice where the pin is go1.26.5 (also caught by R-6). |
| D-5 | `docs/spec-divergence-ledger.md` L-011 | books an owed latitude-inventory entry (item (c)) that has **no `###` row at this tip**. Its content is carried by I-4 and E7's adjacency, so the substance may be discharged — but the ledger's own Owed list is not visibly closed. |
| D-6 | language ledger §2 | numbers two Package_initialization (c)-pins "C1" and "C2", colliding with the latitude inventory's C1/C2. Disambiguated by cross-ref, but a bare-token misread is easy. |
| D-7 | `baselines/negative-full.tsv` | recorded 2026-08-18 against native-full's 2026-08-21. Not an error — the negative lane genuinely did not move — but two baselines diffed by the same gate carry different provenance dates, and only one carries the tip's. |
| D-8 | `docs/wp-arc-log/INDEX.md:234` | claims Kit axiom pins are "240 … at `8b36bf15`, at `69ef4bda` **and at HEAD**". **Re-verified at this tip with the INDEX's own command: 245.** The commit-qualified halves are right; the bare "at HEAD" is precisely the tip-relative cite the same file's conventions block forbids. |
| D-9 | `proofs/Audit.lean:1978-1980` | "the differential (zero drift on the full corpus — **872 cases as of 2026-07-31**)" against 2343 today. Date-qualified, so honest — and a textbook recurrence of the drift the same sentence narrates. |
| D-10 | `docs/2026-08-02_comparator-judge-sprint.md:408-415` | still records the dot-in-path judge bug as *"Owed to the next arc that touches the judge wrapper"*; it was **fixed** at `scripts/comparator-judge:167-170`. The owed-item text was never retired. |
| D-11 | `GoLean/GoCore/EnumDedupCheck.lean:19-27` | describes the certified fragment as **N-OBL + N-L4 only**, omitting **N-APP** — which `innerVecs` implements and `EnumDedupSound.lean:125-258` proves. A trust-surface docstring under-describing the fragment it certifies. On no findings list anywhere. |
| D-12 | `proofs/Audit.lean:992-1000` | the parenthetical "(+ the nil form …)" followed by "Witness `wp_map_range_enter_committed`" reads as though the nil law is witnessed. It is not. |
| D-13 | `Laws/Range.lean:93`, `Laws/StmtOps.lean:208` | **two user-facing laws with neither a witness nor a scaffold marking** — `wp_map_iter_done_nil` (carries `@[go_walk_law]`, zero applications, not named in `Audit.lean` at all, so not even the deletion tripwire sees it) and `wp_map_range_enter_nil`. See §1.3. |
| D-14 | `docs/2026-08-20_machine-twin-harness-design.md:3` | "Status: DESIGN, not built" is stale — §1–§4 are built and §5 executed. The doc has no status-line update, though its D-12 bullet carries a dated correction. |
| D-15 | same file, §5 | says "eleven" fail-closed stubs; the measurement is ten, corrected in place in `docs/raft-w42-log.md` but not in the design text. The number of record is right; the design text is stale. |
| D-16 | `docs/raft-w42-log.md:679-681` | "the only commit after it is the one that writes these two sentences (docs-only, this file alone)" — there are **two** commits after the gated one. Both are docs-only, so the gate-of-record argument survives; the sentence is false at the tip. Self-referential prose that cannot terminate, as the paragraph itself concedes. |
| D-17 | design `:487` vs `docs/raft-w42-log.md:424` | **"456 of the 506 non-`log-level` blocks, 90.1%"** vs **"268 blocks (48.0%) inside supported prefixes"**. These answer different questions — handler-set block coverage vs supported-PREFIX coverage, which truncates at the first unsupported command — but **no document says so**. The 7→6 whole-trace discrepancy IS reconciled; this one is not. |
| D-18 | `docs/raft-w41-log.md:70-91` | **"DISCHARGED 2026-08-21 … exit 0, PASS"** and **"The RUN is still owed, with the same command"** in the same bullet. Reading in order: the 5-type run discharged, then the audit widened to 9 types, and the widened run is owed. The header word is unqualified and the ledger row repeats it as covering all nine. A scoping-doc requirement hangs on this. |
| D-19 | `raftsubject/README.md:48-49` | cites `difftest.py` as validating `plain_clone.go` against the real protobuf runtime with no mention of the sandbox constraint or the owed 9-type run — a cross-doc cite reading stronger than the lane log's own record. |

### What the reconciliation did NOT check, and should be checked by hand

- **That the tracked baseline still matches a run at this tip.** The
  branch's last gate used `GOLEAN_ALLOW_NO_DIFF=1` (legitimately —
  docs-only). Every count in this dossier is read off the RECORD. One
  full `scripts/ci --diff` at the settled tip is the cheapest single
  action that would make the whole of §1.1 first-hand.
- **Whether any spec anchor resolves to a MISQUOTED clause.** The lint
  is resolution-only by construction and says so; the P2 audit found
  five such misquotes it structurally cannot see.
- **Whether the 15 unmapped reds (R-3) are benign.** The tool proves the
  count does not close; only a read decides whether each new red is a
  frontier row's growth, a Q row's, or something nobody has a row for.
- **Whether R-4's four PASSing FR-5/FR-8 citations mean those features
  landed.** If so, two FR rows and two queue positions should retire —
  including the one marked **raft-path TOP** — and the build queue that
  the campaign will consume is wrong at its head.
- **Whether the 64 off-pin version sites (R-6) include a NUMBER-PRODUCING
  claim.** 56 of them are one scheduling dossier's probes on `go1.26.7`;
  if any of its conclusions feed an envelope argument, the argument was
  made on a toolchain the spec pin does not cover.

---

## §3 THE RESIDUALS REGISTER

**The standard this table is held to:** zero items known to the dossier
but absent from it. Where an item is a FAMILY whose members are already
enumerated in a tracked ledger row-by-row (the 15 FR rows, the 10 Q
rows, the 7 T rows, the 34 coverage-ledger areas), the family gets one
row here that points at its ledger — the enumeration is not duplicated,
because a duplicated enumeration is a second thing to drift.

**Launch-relevance** is a GUESS in three values:
**blocking** (the campaign cannot honestly start, or start with the
statement it intends, until this moves) · **recorded** (known, written
down, and the campaign can proceed with it open, provided the statement
says so) · **post-launch** (real work, no bearing on whether the
campaign may begin).

**Count: 216 rows — 77 blocking, 123 recorded, 16 post-launch.**
Derived, not asserted: the counts come from parsing this section's own
tables (`rows starting '| ' minus headers and rules`, bucketed on the
relevance column). The first draft of this line said "148 / 33 / 92 / 23"
from memory before the tables were written — it is left recorded here
rather than silently corrected, because it is maxim (i)'s exact failure
mode caught inside the document that reports maxim (i)'s failures. A few
rows carry a qualified relevance ("mixed; FR-5/9/14 blocking for raft")
and are bucketed as blocking by the parse; treat 77 as an upper reading.

### §3.1 On Mike's desk — decisions the campaign may not make (13)

| # | item | where tracked | relevance |
|---|---|---|---|
| M-1 | **Ratify the constitution** — all 8 §8 sign-off questions open; the draft is 48 commits behind `main` and unreferenced from it | constitution §8 (`proof-constitution` lane) | **blocking** |
| M-2 | Q1 the base predicate (S1–S3 per-step + S4 completion witness) | constitution §8.1 | **blocking** |
| M-3 | Q2 the tier ladder T1→T4 and which T3 invariants are HEADLINE ends | constitution §8.2 | **blocking** |
| M-4 | Q3 the network envelope tier (reliable-first pinned, chaos as strengthening) | constitution §8.3 | **blocking** |
| M-5 | Q4 the RawNode serialization narrowing — accept as v1 fine print or require the widened `harvest` event first | constitution §8.4; machine-twin §2 | **blocking** |
| M-6 | Q5 the liveness tier — in-campaign or named successor | constitution §8.5 | **blocking** |
| M-7 | Q6 the milestone set for audit cadence | constitution §8.6 | **blocking** |
| M-8 | Q7 the supervision seam — trust-surface work supervised vs whole campaign autonomous | constitution §8.7 | **blocking** |
| M-9 | **OQ5 — what `nonterm=` MEANS under `engine=dedup`.** No default stated; *"changes what a green row asserts"*. THE WEDGE row stays on DFS until ruled, and the membership singleton-guard exemption rides on it | `docs/2026-08-20_w32-re-envelope-charter.md:610-638`; `docs/w32-log.md:864` | **blocking** (claim standard) |
| M-10 | **The 22 G3 dossier DISPOSITIONS** (E2–E13, R1–R14, U-4, U-7) are PROPOSALS "batched for the user's ruling"; no ruling-session record exists in the tree | `docs/gallery-campaign-log/g3.md:340-364` + 22 `docs/2026-08-15_dossier-*.md` | **blocking** (a pending decision batch nobody has ruled) |
| M-11 | The confluent-lane `tier=slow` widening + the slow-timeout 3600 default — GATE-SURFACE changes made in lockstep, flagged for the audit | `docs/w32-log.md:604-610` | **blocking** (gate surface) |
| M-12 | The BUG-065 five: §5c sampled fallback (drafted then REVERTED) vs budgets vs the reduction lane | `docs/w32-log.md:604-610` | recorded |
| M-13 | Designation of any new headline (incl. `checkCertM_slowObs`, and the 18 undesignated gallery entries) | `proofs/Audit.lean:261-396`; `docs/verified-examples.md:104-147` | recorded |

### §3.2 Open fidelity bugs (8) and their in-entry residuals (10)

| # | item | where tracked | relevance |
|---|---|---|---|
| G-1 | **BUG-062** — inline `len`/`cap` reads reorder against calls: a FORCED-point silent wrong answer (machine 3 vs go 1). Receive-bearing functions are right only by accident | `docs/BUGS.md:2932`; 2 differential reds | **blocking** |
| G-2 | **BUG-002** — expression-step atomicity wrong for concurrent Go (latent). Structural root fixed; STILL OPEN: goroutine rules + scheduler `Choices`, and the granularity-ledger re-audit of multi-cell apply steps | `docs/BUGS.md:2506`; Q-ATOMICITY; master plan C-D | **blocking** |
| G-3 | **BUG-008** — imported named types have no wire declaration, so comparability is UNKNOWN | `docs/BUGS.md:2137`; FR-9 | **blocking** (raft imports named types pervasively) |
| G-4 | BUG-061 — the pruning rule under-approximates `staticinit`; 11 of 26 init flavors residual, one un-chaseable | `docs/BUGS.md:33`; ledger L-011 | recorded (area is LATITUDE; gc not single-valued) |
| G-5 | BUG-059 — panic messages render TypeId qualifiers as the import PATH not the package NAME; structural fix = separate DISPLAY from IDENTITY in GoCore | `docs/BUGS.md:139` | recorded |
| G-6 | BUG-041 — race-footprint over-approximation: value-path composite reads are whole-cell (over-REFUSAL, never a missed race) | `docs/BUGS.md:920`; Q-RACEPATH | recorded |
| G-7 | BUG-004 — panic abort rendering: items 1 (eface allocation identity), 3 (multi-line payloads), 4 (`preprintpanics` method call) open | `docs/BUGS.md:2395`; (c)-row C4; A7 | recorded |
| G-8 | BUG-065 — exhaustive envelope certification tractability, NARROWED to `goroutines/worker-pool/sum` (>9.5M nodes, no closure) | `docs/BUGS.md:3090` | recorded (1 confluent red) |
| G-9 | BUG-021 residual — the append-spill envelope is known TOO NARROW; no shipped theorem walks the spill path yet, so the hole is latent. Fix = widen to `[newLen, max(32, 2*growthFormula)]` | `docs/BUGS.md:1652` | **blocking** (too-narrow = the soundness direction) |
| G-10 | BUG-009/008 shared owed sub-slice — emit declarations for imported non-interface named types | `docs/BUGS.md:2135` | **blocking** |
| G-11 | BUG-009 residual — a method declared in a `_test.go` file is excluded by `nonTestGoFile`, leaving a KNOWN type with an incomplete method set | `docs/BUGS.md:2126` | recorded |
| G-12 | BUG-007 owed sub-slice — forwarding entries for the promoted method set (detecting promotion soundly is the real fix) | `docs/BUGS.md:2215` | recorded |
| G-13 | BUG-006 residual — two multi-value-assign tuple interface sites still REFUSE | `docs/BUGS.md:2230` | recorded |
| G-14 | BUG-005 residual — delete-prune rewrites only same-goroutine frames; the widening is OWED at the first non-racy cross-goroutine shape | `docs/BUGS.md:2274`; latitude E9 | recorded |
| G-15 | BUG-005 kit obligations — the termination theorem *"body stores no key into the ranged map ⇒ range terminates"* is recorded, not proven; stop-admitting / mutating-range WP laws owed | `docs/BUGS.md:2283` | recorded |
| G-16 | BUG-057 residual — six shapes STILL RED, all fail-closed | `docs/BUGS.md:2812` | recorded |
| G-17 | BUG-049 deferred — multi-value assign / var-decl-from-call / plain chan-receive interface forms fail closed with quarantine messages | `docs/BUGS.md:458` | recorded |
| G-18 | grossmith F-1 — BUG-062's statement is `len`/`cap` only; the `min`/`max` VALUE divergence is unpinned and mini-slice A6's scope is known-incomplete | `TODO.md:818`; `docs/2026-08-20_grossmith-findings-2.md` | **blocking** |

### §3.3 The latitude / envelope census — 51 rows

38 of the inventory's 39 `###` entries (E1 is (c) FORCED with nothing
owed), plus the int-width records flag, the five class-(d) unknowns,
three doctrine registers, the I-4 adopted reading, the ledger's external
debt, the frame theorem's quotient condition, and the uncensused C42
question.

The inventory is the register; this table names only what is not
discharged. Class per `docs/2026-08-11_latitude-inventory.md`.

| # | item | where | relevance |
|---|---|---|---|
| L-C1 | L1 scheduler pick enveloped only at REGISTRY granularity; full interleaving vs registry-point path set is the open NPDRF obligation | LI:94-122; register #5 | **blocking** |
| L-C2 | back-edge boundaries landed; residual = SUB-STATEMENT granularity | LI:124-183 | recorded |
| L-C3 | `.opDone` boundaries landed; residual = B3, the abort WINDOW at panic terminals, DEFERRED at G1 | LI:185-232 | recorded |
| L-C4 | L5 main-exit window maximal only at registry granularity | LI:234-252 | recorded |
| L-C5 | L4 waiter pick — the open [ANALYSIS] "is L4 ⊆ L1-reachable" (= U-2); no theorem | LI:254-272 | recorded |
| L-C6 | L2 select weakened from "uniform pseudo-random" to possibilistic; distributional facts out of scope BY DECLARATION | LI:274-294 | recorded |
| L-C7 | (b-n) woken select head-commits; the coverage argument is [ANALYSIS] not a theorem and must be RE-ARGUED whenever wake machinery changes | LI:296-318 | recorded |
| L-C8 | CONTAINED DIVERGENCE — gc reader-first vs our writer-first at a both-parked RWMutex; TryLock's spurious-failure member unmodeled | LI:320-350; Q-TRYLOCK | recorded |
| L-C9 | deadlock detect-vs-hang pinned to gc (permanent-pin territory) — **and omitted from §10's own (b) count** (§2 R-5) | LI:352-372 | recorded |
| L-C10 | racy-program refusal targets TSan's REALIZED edge set, not go_mem's minimal relation; scope-ledger U2/U4/U5/O1 open | LI:374-411; register #13 | recorded |
| L-C11 | heap addressing DISCHARGED by quotient — **conditionally**: modeling `%p`, pointer ordering, unsafe int↔ptr, or any address-exposing channel RE-OPENS it | LI:429-444 | recorded (re-opening condition) |
| L-E2 | (b) gc call-first; obligation = a two-point-or-wider envelope at the call rules; 5 timing pins → membership rows | LI:477-505; OQ4 | post-launch |
| L-E3 | **(b) PINNED to OUR point, KNOWN ≠ gc, gc's realization UNPINNABLE** | LI:507-535 | **blocking** (soundness direction) |
| L-E4 | (b) targets-vs-RHS unordered panic; same mechanism as E3 | LI:537-545 | **blocking** |
| L-E5 | **(b) spec-literal point; gc lands ELSEWHERE** (gc takes the early store) | LI:547-562 | **blocking** |
| L-E6 | REFUSED: `len`/`cap` hoist in receive-bearing functions — a COVERAGE DEBT existing only because E3/E4's linearization is unbuilt; reach includes idiomatic `len(p.xs)`, kills whole-package export | LI:564-573 | recorded |
| L-E7 | **(b) go/types' order, KNOWN ≠ gc, and UNGUARDED** — no frontend check detects the shape; `etcd-io/raft` has package-level vars. A cheap interim detector exists | LI:575-607 | **blocking** |
| L-E8 | (b-n) multi-file order narrowed to the go command's sort-by-name | LI:609-618 | recorded |
| L-E9 | RE-ENVELOPED 2026-08-19; residual = the SAME-GOROUTINE-only delete-prune; *"widen or justify at the first cross-goroutine-range case not already racy-red"* | LI:653-659 | **blocking** (a named W3.2 DONE clause) |
| L-E10 | (b) always-replace map-key retention | LI:661-677 | recorded |
| L-E11 | (b) runtime-check order inside one operation | LI:679-692 | recorded |
| L-E12 | (b) structural (frontend ANF). **Census follow-ons NOT censused**: composite-literal element order vs a call among elements; duplicate-map-key eval order; map-literal key-vs-value order | LI:696-754 | recorded (census gap) |
| L-E13 | **(b) structural, KNOWN ≠ gc on the type-assertion axis — "NO PIN MAY BE TAKEN HERE"**, census row only, no corpus case. Census follow-on not claimed: div-by-zero, slice-to-array, nil-map write, nil deref vs sibling calls | LI:756-830 | **blocking** |
| L-R1 | (b) int/uint = 64 bits; obligation = parameterize width; blocked on any 32-bit oracle | LI:834-857 | post-launch |
| L-R1b | the int-width pin has **no site-level record** — `Value.lean:33` carries no caveat the singleton-narrowing rule would require | LI:1299-1302 | recorded |
| L-R2 | (a) ENVELOPED but DELIBERATELY NOT MAXIMAL — a pragmatic subset of the spec's unbounded append latitude | LI:859-875 | recorded |
| L-R3 | **(b-n) `[]byte(s)` cap singleton with gc KNOWN OUTSIDE on the escaping path; the RUNE arm has no agreeing pin at all** (`cap([]rune("héllo"))` = 32). Priority 4, "best value-per-cost" | LI:877-901; OQ4 | **blocking** |
| L-R4 | (b-n) float fusion narrowed to per-op rounding, platform-scoped to linux/amd64 GOAMD64=v1; arm64 and amd64-v3 executions of fusable shapes are OUTSIDE the envelope | LI:903-919 | recorded |
| L-R5 | (b-n) float div-by-zero narrowed to no-panic; complex division is the re-opening condition | LI:921-929 | recorded |
| L-R6 | REFUSED float→int out-of-range/NaN; re-envelope = a VALUE envelope. 2 permanent reds | LI:931-940 | recorded |
| L-R7 | NaN payload pinned canonical quiet; becomes latitude-relevant if `math` lands | LI:942-953 | recorded |
| L-R8 | (b) WaitGroup counter pinned to gc's int32-wrap bit layout | LI:955-968 | recorded |
| L-R9 | (b) panic values/message texts pinned to gc's strings, with a STANDING caveat that no message-content claim transfers beyond gc | LI:970-988 | recorded |
| L-R10 | (b) abort-line rendering pinned to `preprintpanics`; *"the re-envelope obligation is really BUG-004's fix list"* | LI:990-1002 | recorded |
| L-R11 | (b) sync-misuse fatal class; recorded narrowing — the observation DROPS gc's pending-panic line during unwinding | LI:1004-1021 | recorded |
| L-R12 | (b) exit codes / terminal classification pinned at the harness boundary | LI:1023-1028 | recorded |
| L-R13 | sortSlice insertion sort: declared-unobservable narrowing **scoped to INT kinds** — real latitude the day non-integer sorts land | LI:1030-1037 | recorded |
| L-R14 | (d) UNKNOWN constant-arithmetic precision, delegated to go/types; extremes NOT analyzed (= U-3) | LI:1039-1049 | recorded |
| L-R15 | **(b) zero-size address identity pinned never-same; gc probed NON-single-valued** (escaped compare EQUAL via `runtime.zerobase`). Standing red | LI:1051-1079 | **blocking** |
| L-U2 | L4 ⊆ L1-reachability: no theorem, no counterexample search | LI:1128-1130 | recorded |
| L-U4 | overlapping copy/append aliasing: FORCED by spec, but the differential coverage validating the multi-cell one-step arms is OWED (5 concrete cases handed over) | LI:1132-1136; `g3.md:324` | post-launch |
| L-U5 | **wide-op granularity under concurrency** — `appendSlice`/`copySlice`/`clearSlice` are single apply steps; the granularity-ledger re-audit before any concurrency claim mentioning them is STILL OWED (BUG-002's R4 residue) | LI:1137-1143 | **blocking** |
| L-U6 | future atomics: the latitude to analyze is the surrounding-plain-access envelope | LI:1144-1151 | post-launch |
| L-U7 | **gc VERSION DRIFT as an evidence problem** — every pinned realized point assumes its version-tracking pin actually fires on toolchain movement; believed true, **NOT re-audited** | LI:1152-1156 | recorded |
| L-REG3 | doctrine register #3 — one-implementation evidence base; no XIMPL lane exists | doctrine:125-127 | recorded |
| L-REG5 | doctrine register #5 — registry/back-edge scheduling granularity; gaps = B3 + sub-statement | doctrine:136-142 | **blocking** (a named W3.2 DONE clause) |
| L-REG7 | doctrine register #7 — unbounded memory / allocation never fails; STANDING IDEALIZATION, explicitly NO obligation | doctrine:156-173 | recorded |
| L-SPEC | adopted reading I-4 — the `multipkg/init-order-*` pins are gc-at-default-flags realizations, *"re-envelope obligation open"* | `docs/spec-interpretations.md:92-102` | recorded |
| L-FRAME | the executable frame theorem's `nextAddr` bump is scaffolding DISCHARGED BY QUOTIENT, conditional on the modeled observation surface | `docs/2026-08-13_executable-frame-theorem.md:302` | recorded |
| L-LDG | ledger externals — L-007/L-008/L-010 spec errata UNREPORTED; L-014 gc-bug UNFILED (pending Mike); L-015 recorded-not-filing; L-011 `Status: open` with three owed items | `docs/spec-divergence-ledger.md` | recorded |
| L-C42 | OPEN census question deliberately not ruled: send-statement channel-vs-value evaluation order may be a frontend PIN, not a forced order; the corpus pins one order | `docs/2026-08-21_w7-desugar-inventory.md:3042` | recorded |

### §3.4 The raft ladder (W-series) — 17

| # | item | where | relevance |
|---|---|---|---|
| W-1 | **W4.3 (the twin, n=3, reliable-first) — NOT STARTED**; the `raft-w43` worktree has zero commits. This is M1 and most of M3's mechanism | machine-twin `:566`; `git worktree list` | **blocking** |
| W-2 | **W4.4 (the trace differential) — NOT STARTED** | machine-twin `:574` | **blocking** |
| W-3 | **W4.5 (the envelope) — NOT STARTED**: jitter latitude entry, network-draw latitude entries, perturbed-stream battery, the §6 footprint check against its 5-item checklist, the §2 harvest-atomicity re-envelope | machine-twin `:582` | **blocking** |
| W-4 | **The §6 shared-nothing footprint check is NOT MECHANIZED**, though the design says it must be. Without it the sequential→concurrent reduction is unsupported | machine-twin `:374-423` | **blocking** |
| W-5 | **The W4.2 tier-strength bound** — neither shipped green tier can FALSIFY the replay mirror; its fidelity rests on code reading | `docs/raft-w42-log.md:491-520` | **blocking** for W4.3's framing |
| W-6 | 0 of the 309 rendered-expectation blocks render today; the 58 pure-log-line blocks CANNOT be reproduced without a RECORDING logger, which re-opens the §6 check | `docs/raft-w42-log.md:562-587` | **blocking** for the full trace tier |
| W-7 | Conf-change support (propose-conf-change + ApplyConfChange) unlocks 11 more traces — the largest single stopper class | `docs/raft-w42-log.md:626` | recorded |
| W-8 | **Interpreter WALL TIME bounds the whole raft instrument family** (`probe_and_replicate` ~1 h; twin groups 20–24 min); *"Nothing here lands in a gate today."* The real answer is an interpreter-performance pass or a compiled evaluation path | `docs/raft-w42-log.md:638-648` | **blocking** for ever gating the raft instruments |
| W-9 | W5 (the concurrent twin: real pipeline, network chaos, schedule-fuzzing gate) NOT STARTED as chartered; W5.2's latitude entries unwritten | master plan `:180-190` | **blocking** for M3 |
| W-10 | **W6 (statement & pinning) NOT STARTED** — §8 rulings unobtained, the statement not elaborated, `scripts/check-raft-goal` absent | master plan `:192-203` | **blocking** for M5 |
| W-11 | W1.2 `slices.SortFunc` shim/extern — OPEN (= hole H-5) | master plan `:130` | recorded |
| W-12 | W1.3 stage-by-stage sweep of `raft.go` for lowering refusals — only partially done via the W4.0/W4.1 censuses | master plan `:132` | recorded |
| W-13 | W3.3 granularity per C-C: the wedge fix DONE; **register #5's ruling OPEN; BUG-002's disposition OPEN** | master plan `:167` | **blocking** for M4 |
| W-14 | Milestones **M2, M3, M4, M5 all OPEN** (M1 essentially reached via W4.1+W4.2). M5 *is* the launch gate the constitution names | master plan `:205-221` | **blocking** |
| W-15 | Five pre-registered risks still live: `raft.go` scale surprises; re-envelope breakage of proof estates; U-2 turning out load-bearing; protobuf strategy churn; two-lane contention / statement drift | master plan `:253-276` | recorded |
| W-16 | `raftharness` known coverage gap — the crash-restart victim stops at a quiescent point, so committed-but-unapplied crash state is never produced and its anomaly guard is never live | `raftharness/README.md:119-125` | recorded |
| W-17 | Transitive quarantine shape (`var x = quarantinedSourceFn()`) deliberately OUT of v1; widening owes a FRESH EFFECT ARGUMENT | `docs/raft-w4-log.md:170-177` | recorded |

### §3.5 W3.2 — the single load-bearing blocker (9)

| # | item | where | relevance |
|---|---|---|---|
| X-1 | **Slices 2, 3, 4, 5, 5b, 6 of a 7-clause DONE conjunction are UNSTARTED.** They own E3/E4/E5, E7, E9's residual, R3, R15, register #5/NPDRF, the C1–C8 routing, the C5 and rendering rulings, and BUG-065's principled fix. Almost nothing in §3.3 retires without it | `docs/2026-08-20_w32-re-envelope-charter.md:645-663` | **blocking** |
| X-2 | Slice 2 — the eight Q-row design questions, all unruled (`w32-qrows` worktree, 0 commits) | charter `:264` | **blocking** |
| X-3 | Slice 3 — init-order envelope + detector + membership rows; the four rendering rows' R-1 conversion; the C5 ruling; the queue tail | charter `:304` | **blocking** |
| X-4 | Slice 4 — E9's cross-goroutine widening residual (widen or justify) + guardrail case | charter `:400` | **blocking** |
| X-5 | Slice 5 — registry-granularity scheduling-point completeness + the register #5 / NPDRF ruling (a theorem or a scoped docstring) | charter `:415` | **blocking** |
| X-6 | Slice 5b — the second PL-nitpicker review, added at G0 by Mike (`w32-5b` worktree, 0 commits) | charter `:442` | **blocking** |
| X-7 | Slice 6a — the LaTeX opsem write-up, HELD for the Lean-SpecTec prototype (a deliberate hold, not a gap) | charter `:453`; roadmap `:409` | recorded |
| X-8 | Slice 6b — iris-lean pin refresh + reuse survey; may force a comparator/lean4export re-pin needing separate approval | charter `:494-509`; `TODO.md:783` | **blocking** for channel-logic resume |
| X-9 | `NPDRFReduction` ships as a DRAFT, REFUTABLE-AS-WRITTEN `Prop`-valued def with 6 recorded obstructions; nothing may cite it — and it is BUG-065's and register #5's fix path | `GoLean/GoCore/NPDRF.lean:40-120` | **blocking** |

### §3.6 Holes — the three `H-` registers (17 open)

**Naming hazard, carried forward for the audit:** three colliding
registers use `H-<n>` — the raft handoff (H-1…H-20), the hole census
(H-a…H-f), and the W7 desugar inventory's Chapter H (H-1…H-6). Cite
the file.

| # | item | where | relevance |
|---|---|---|---|
| H-1r | difftest.py §7 vs the REAL protobuf runtime — see D-18 for the DISCHARGED-vs-still-owed contradiction | `docs/raft-w41-log.md:705`, `:794` | recorded |
| H-3r | method STENCILS of generic types fail the WHOLE export (`mono.go flushTypeInsts`) = FR-4 | `docs/raft-w3-log.md:535` | recorded |
| H-5 | `slices.SortFunc` unmodeled (`MajorityConfig.Describe`) — measured OFF the twin's path | `docs/raft-w3-log.md:537` | recorded |
| H-6r | the fmt matrix's two boundary rows are the widening protocol's entry point; `%X` still refused (a two-site invariant that owes differential pins) | `docs/holes-arc-log.md:268-284` | recorded |
| H-7 | covmap for the subject↔upstream delta ledger: the per-line delta view was never built (SHA-256 digest pins used instead) | `docs/raft-w2-log.md:613` | recorded |
| H-8 | `raftsubject/` is in NO gate — `derive.py --check` / `difftest.py` / `frontier.py` reproduce on demand but nothing runs them; the honesty-of-derivation claim is ungated | `docs/raft-w2-log.md:614` | **blocking** |
| H-12r | `sync/escapes/{method-value,go-stmt}` remain the sync fail-closed frontier; chan-typed bare-nil ops recorded UNTESTED | `docs/raft-w41-log.md:662` | recorded |
| H-15r | **the jitter RANGE latitude entry `[electionTimeout, 2*electionTimeout)` is NOT written** | `docs/raft-w41-log.md:735`; `raft-w42-log.md:614` | **blocking** (master plan C-B) |
| H-19 | `node_decls.go` keeps `ErrStopped` for chunk granularity; splitting the `var(...)` block costs a sub-declaration delta | `docs/raft-w3-log.md:549` | recorded (defanged) |
| H-20 | **NEW** — no sound effect/isolation story for WRITER-TYPED package-level globals; replaces the FALSE "H-11 retires D-12" claim. The honest alternative recorded beside it is to leave D-12 permanent | `docs/raft-w42-log.md:603-613` | recorded |
| H-20g | H-20's guardrail corpus row (the D-12 refusal must stay a WHOLE-export refusal) is OWED and unlanded | `docs/raft-w42-log.md:599` | recorded |
| H-a-r | WIDENED REFUSAL recorded with the H-a fix: nil pointer-to-array elided-high slices moved from an accidental gc-matching panic to an honest STUCK; **the B-33 `emitAddressOf` StarExpr-collapse hole stays OPEN** | `docs/holes-arc-log.md:10-25` | recorded |
| H-c | two missing decoder checks — duplicate-TypeId sweep, and literal element-index bounds (the spurious-panic direction); *"still owed, W7 tier-0"* | `docs/2026-08-21_w7-desugar-inventory.md:2912` | recorded |
| H-e | composite-literal element order vs a sibling call's panic: probed NOT a divergence, but an UNCENSUSED latitude point the spec states explicitly | `docs/2026-08-21_w7-desugar-inventory.md:3000` | recorded |
| H-f | **struct TAGS dropped from the wire — a genuine identity collapse in `Ty`; observability NEVER PROBED.** Owes a witness attempt or an argued-unobservable narrowing | `docs/2026-08-21_w7-desugar-inventory.md:3017` | **blocking** (an unprobed identity collapse in the trust surface) |
| H-invH2 | the quarantine rollback set has THREE recorded unrestored gaps (`syncUsed`, `importedNamed`, `badKeyPaths`); conservative direction, no corpus case reaches one | `docs/2026-08-21_w7-desugar-inventory.md:2535` | recorded |
| H-invH5 | init code has NO per-declaration quarantine — one unsupported init body refuses the whole export; a real coverage cliff at multi-package scale | `docs/2026-08-21_w7-desugar-inventory.md:2549` | recorded |

### §3.7 Parks (12)

| # | item | where | relevance |
|---|---|---|---|
| P-1 | **channel-logic ARC PARKED** — ~14.5k lines of concurrency WP laws + the compositional flagship; 34 ahead / 451 behind. Resume condition HALF MET (blocker 1 done 2026-08-12; blocker 2 = W3.2, in flight) | `channel-logic` branch charter `:276` | recorded |
| P-2 | `channel-logic-s4` parked unmerged; its tip's citable-target claim was REFUTED. **Salvage the families, never merge as-is** | `channel-logic-s4` branch; `docs/2026-08-20_w32-boundary-set.md:93` | recorded |
| P-3 | **The channel-logic RESUME-READINESS assessment (§S6c) does not exist yet** — the proof re-alignment bill, statement survival, salvage plan and reduction-line re-target are all unsized. This is the artifact the resume condition names | charter `:510-524` | **blocking** for the resume |
| P-4 | `spec-parity-s2` PARKED RED — `MachineSound` has 16 open proof errors on a branch | `TODO.md:749` | recorded |
| P-5 | goose-parity P2 PARKED by user ruling (no cap raises); resume condition = partial-order reduction. The W3.2 POR slice is a partial mover but no revisit is scheduled, and any revisit is explicitly a USER decision | `docs/goose-parity-parked.md:58-61` | recorded |
| P-6 | Kit: **key-generic `MapMem`/`MapLoops` parked with THREE pullers** — the ≥2-consumer consolidation slice is OWED and unscheduled, i.e. the promotion rule's own trigger has fired and nothing has consumed it | `docs/kit-guide.md:741-750` | recorded (resume condition IS met) |
| P-7 | Kit: element-kind-generic `SliceMem` parked, no puller | `docs/kit-guide.md:751` | post-launch |
| P-8 | Kit: **struct-cell / value-side generalization parked — "expected to matter more than key-genericity at the raft target"** | `docs/kit-guide.md:757` | recorded (a named raft-path risk) |
| P-9 | Kit: choice-dependent LAYOUT (data-dependent allocation addresses) has no address-shift simulation | `docs/kit-guide.md:753` | recorded |
| P-10 | P-S3-5 parked — the joint sequential "completes AND verdict" form is derivable but not claimed | `docs/2026-08-10_wp-walk-driver.md:114` | recorded |
| P-11 | spec-parity-s6 parked set: the `&&`/`\|\|` short-circuit WP law family (blocks two named units); P-S4-1/2's channel WP safety half; **71 unpinned units**; `GoldenSelectDone`'s literal-fuel statements | `docs/2026-08-10_spec-parity-s6.md:154-163` | recorded (the 71-unit lever is a user scale call) |
| P-12 | example-spec-form §8 + examples-phase2 parked sets: the `$forFirst` desugar tax; two designation CANDIDATES not designated; the gallery renderer; recursion/nested-loop termination + tactic packaging; short-circuit call-hoisting ergonomics; `fmt.Sprint`; the differential driver past int64; NativeToIR annotation parsing; the relational unbounded-data mechanism; the raft capstone conditioned-Agreement form | `docs/2026-08-12_example-spec-form.md:950`; `docs/2026-08-14_examples-phase2-arc-charter.md:228` | post-launch |

### §3.8 Proofs, kit and statement TCB (23)

| # | item | where | relevance |
|---|---|---|---|
| K-1 | **`wp_map_iter_done_nil` — a `@[go_walk_law]` user-facing law with no witness, no scaffold marking, and no mention in `Audit.lean`** | `Laws/Range.lean:93` | **blocking** (a live non-vacuity-gate violation) |
| K-2 | **`wp_map_range_enter_nil` — same class**; the gate cites the LAW, and the witness it names discharges the non-nil form | `Laws/StmtOps.lean:208`; `Audit.lean:1069` | **blocking** |
| K-3 | **Witness EXISTENCE is unmechanized** — deletion is gated, existence is not; ~80 of 300 gate lines name a law rather than an instantiation, and 60 of 123 `wp*` laws are never named in `Audit.lean` | `proofs/Audit.lean:905-1074` | **blocking** (the doctrine's own defence rests on the manual audit it exists to replace) |
| K-4 | **The comparator landmark is 371 commits stale AND the statement TCB moved under it** — three new `Expr` constructors, a `Value.lean` change, and a change to `Examples/Targets.lean` INSIDE Challenge's closure. The landmark trigger is scoped to designated-set/statement changes, so a GoCore change that alters every designated statement's closure does not fire it | `docs/2026-08-02_comparator-judge-sprint.md:373`; `git diff e42020397648..HEAD` | **blocking** (cheapest high-value pre-launch action: re-run `scripts/comparator-judge`) |
| K-5 | `Challenge`/`Solution` are **not default Lake targets**, so `scripts/ci` never builds them; the 56-way lockstep is checked only inside the comparator | `proofs/lakefile.toml:42-46` | recorded |
| K-6 | **`SlowObs`/`checkCertM_slowObs` is not DESIGNATED** — the strongest new claim on the branch, and what every `engine=dedup` record MEANS, is never comparator-replayed and never walked by the statement-TCB gate | `GoLean/GoCore/EnumDedupSound.lean:944`; `proofs/Audit.lean:619` | **blocking** (the constitution's own ideology points here first) |
| K-7 | 18 of 26 gallery headlines UNDESIGNATED — deletion tests run by hand, never gate-walked, never comparator-replayed | `docs/verified-examples.md:104-147` | recorded |
| K-8 | The readout-corollary mandate, "no kit name in a headline closure", and deletion tests for undesignated theorems are all **unmechanized doctrine** | TCB doctrine `:32`; `docs/kit-guide.md:9` | recorded |
| K-9 | `EnumDedupCheck.lean:19-27` under-describes the certified fragment (omits N-APP) — a trust-surface docstring understating what it certifies | `GoLean/GoCore/EnumDedupCheck.lean` | recorded |
| K-10 | The `# params-note` warning in the certified record is deliberately invisible to the record parser's `# params:` extraction | `baselines/certified/*.certified.tsv` | recorded |
| K-11 | **The blanket `interpreterSound` stays FALSE-AS-STATED** while the interpreter is richer than the relation (e.g. string `add`) | `TODO.md:246` | **blocking** (a false-as-stated theorem inside the trust chain) |
| K-12 | `go_adequacy` covers only NON-PANICKING runs (`.panicked` has no outgoing `Step`, so it counts as stuck) — and raft code panics | `TODO.md:321` | **blocking** |
| K-13 | Arc C Rel completion — D1 seqn-splice (the relation cannot run ANY frontend-lowered program with a declaration), D3 panic propagation, D2-proper result locations | `TODO.md:21` | **blocking** |
| K-14 | D3 correspondence shape (step-indexed / small-step oracle) covering prefixes of nonterminating runs | `TODO.md:281` | **blocking** |
| K-15 | End-to-end adequacy witness + closing `hstore` | `TODO.md:169` | **blocking** |
| K-16 | spec-surface: arity-general `GoFuncSpec` + runner-equivalence lemma; `(T, error)` results queued behind interface widening — **raft returns `(T, error)` pervasively** | `TODO.md:88` | **blocking** |
| K-17 | Ghost / abstract-state machinery + the linearization-point idiom for multi-step protocol updates | `TODO.md:100` | **blocking** for T4 linearizability |
| K-18 | Generate struct typed points-to predicates as field-wise ownership, and field load/store/access lemmas over `Loc.field` | `TODO.md:629-630` | **blocking** for raft structs |
| K-19 | Arc E widening ladder; the spec-surface arc's audit ask + merge sign-off never recorded as done | `TODO.md:112`, `:85` | **blocking** |
| K-20 | **PARKED: `$runtime.Error` method set on recovered runtime panics** — broke all 19 of the review campaign's wrapper-caught panics and blunts grossmith's recover-wrapper surface. *Do NOT drive-by fix* | `TODO.md:634` | **blocking** (raft uses recover wrappers; it also disarms a fuzzing instrument) |
| K-21 | `DedupAdjacent` is an un-retrofitted `stepFnIter_iterate_bail_rel` consumer (two promotion-ledger candidates); the guide's §14 THIRD CLASS has no landed `_rel` consumer; round-2 guide fixes not themselves dry-run tested; the smart-unfolding REVERSAL's discriminating feature was never isolated | `docs/wp-arc-log/{s4,s6,INDEX}.md` | post-launch |
| K-22 | Gobra lane residuals — `Parser.fuelFor` ARGUED not proved (failure mode: a silently false round-trip); the `GoFuncSpec` joint is a SCAFFOLD; `GExpr.eval` gives `x/0 = 0`; loop-invariant scoping unchecked; a second loop breaks `GobraContract`; two corpus extractions disagreed so only "~5%" is defensible | `TODO.md:719-742` | recorded |
| K-23 | Verdi lane — decisions D1/D2/D3/D5 open; the protocol-gap ledger (PreVote, learners, snapshots, CheckQuorum, ReadIndex, leader transfer, fast backoff, heartbeat msg, batching absent in Verdi; four representation deltas) scopes any Verdi-derived transfer; the consensus-proof-translation campaign is the tier-1 target's route | `docs/2026-08-09_verdi-compat-layer.md:392-449`; `TODO.md:701` | recorded |

### §3.9 Instruments, records and process hygiene (24)

| # | item | where | relevance |
|---|---|---|---|
| N-1 | **`compat/gobra` is UNGATED** — zero references in `scripts/ci`; its ~70 `#guard`s and advisory `AxCheck` run only on a human build (`compat/verdi` IS gated) | `scripts/ci`; `TODO.md:690` | recorded (gate honesty) |
| N-2 | A cgroup kill is SILENT — `scripts/capped` execs and cannot observe OOM exit 143 | `TODO.md:670` | recorded |
| N-3 | Still uncapped when invoked directly: `coverage`, `diff-one`, `comparator-judge`, `check-golden`, `check-imported-pins`, `test-import-goose`, `test-lane-validation`, `comparator-setup`, `diff-coverage`, and the Lean language server | `CLAUDE.md`; `TODO.md:681` | recorded |
| N-4 | **`docs/gocore-semantics-upgrade-handoff.md` is DEAD** (last touched 2026-07-18) while `CLAUDE.md` still mandates appending to it | the file; `CLAUDE.md` | recorded (process gate-honesty) |
| N-5 | **`docs/roadmap.md` carries a STALE banner flagged 2026-07-19** — obsolete Gobra framing, wrong Iris phasing, superseded coverage claims; the "full rewrite" task was never done | `docs/roadmap.md:3-13` | recorded (launch-visible) |
| N-6 | roadmap Phase 6 "Lean Output Surface" has no status line and no work anywhere — the user-facing surface | `docs/roadmap.md:329-344` | post-launch |
| N-7 | **Three colliding `H-<n>` registers** — an auditor trip hazard before eight reviewers read in parallel | §3.6 | recorded |
| N-8 | `TODO.md:172` still claims "85 baseline fidelity failures not yet explained"; actual is 15 in three dispositions | `TODO.md:172` | recorded (maxim (i)'s exact class) |
| N-9 | `TODO.md:112`/`:187` still treat BUG-001 as open (fixed 2026-08-18); the Arc D header says IN PROGRESS while its body records the merge; "eval big-step totalization" listed as next while F3 records it DONE | `TODO.md` | recorded |
| N-10 | ~20 further `TODO.md` rows are Gobra-era or superseded and nothing says so | `TODO.md:422-742` | recorded |
| N-11 | **16 dangling `docs/*.md` citations**, two live lane-only | §1.6 | recorded |
| N-12 | The four covmap CIP drafts are "not yet handed to the covmap repo"; the content-hash layer stays validated-but-UNWIRED | `docs/covmap-cips/*.md:5` | recorded |
| N-13 | `Race.lean:588-590` ChanClocks docstring is STALE; the doc-only fix owed at the next Race.lean-touching slice was not made | LI:1290-1298 | recorded |
| N-14 | Deferred hardening, four items never done: corpus mutation/tamper testing, sub-feature read/write tags, a wider observation channel, exact panic-message matching | `TODO.md:170-171` | recorded (gate-strength gaps) |
| N-15 | `scripts/check-coverage` lists 33 all-failing feature tags = unimplemented features; the count is likely stale | `TODO.md:177` | recorded |
| N-16 | Structured-error work owed: replace stringly-typed evaluator failures with `GoError` values; the CLI must not classify by message prefix; thread panic/unsupported/stuck/internal through GoCore | `TODO.md:444`, `:475` | recorded |
| N-17 | Harness hardening owed: a structured observation comparator instead of raw JSON string comparison; timeouts/fuel for each stage; per-run temp dirs with atomic publish tied to source hashes | `TODO.md:449-453` | recorded |
| N-18 | The map-range live-pick walk is ~O(n²) per range, cubic in ∀-stream certification — will bite at raft-scale maps | `TODO.md:143` | recorded (perf) |
| N-19 | Enumerator roadmap: verified POR (BUG-065's principled fix), symmetry reduction with its id-relabeling soundness obligation, preemption-bound-as-metadata (certificates must NAME their bound), state memoization, PCT/portfolio sampling | `TODO.md:133-141` | **blocking** (the POR item) |
| N-20 | Process deviations recorded, not rationalized: W4.1 item 5 committed on a RED gate (B-9); the W3.2 nine-row re-pin landed one commit AFTER the move, against the same-commit rule (B-F11); W4.2 item 1 has no saved gate transcript (B-F7); `--slow` not re-run at the W3.2 audit-fix round (argued unnecessary) | `docs/raft-w41-log.md:684`; `docs/w32-log.md:725`; `docs/raft-w42-log.md:705` | recorded |
| N-21 | **Every W4.2 agreement verdict and gate transcript lives under gitignored `artifacts/w42/`** — the tracked-evidence fix applied to the census was not extended to them | `docs/raft-w42-log.md:358`, `:422`, `:650`; `.gitignore:5` | **blocking** (§1.2's biggest structural finding) |
| N-22 | Only ONE certified-set record exists in the tree | `baselines/certified/` | recorded |
| N-23 | Holes-arc F4 residual — the certified record's open question (what the OLD record was certified under) is UNRECOVERABLE from the file | `docs/holes-arc-log.md:38-47` | recorded |
| N-24 | The 10 tool findings + 19 read-level discrepancies of §2 | §2 | recorded (R-1…R-4 lean blocking) |

### §3.10 Lanes and branches (9)

| # | item | where | relevance |
|---|---|---|---|
| B-1 | `proof-constitution` — the draft, 8 open questions, 48 behind, unreferenced from `main` | branch `dee9eaed` | **blocking** |
| B-2 | **Three arcs branch-complete AWAITING MERGE SIGN-OFF** with the audit ask posed: `holes-arc`, `raft-w42`, `w32-re-envelope` | the lane logs | **blocking** (merge protocol) |
| B-3 | `channel-logic` (34 ahead / 451 behind) and `channel-logic-s4` — parked, see P-1/P-2 | branches | recorded |
| B-4 | `wp-design` (6 ahead / 217 behind) — holds the symbolic-domain design note, the OQ3 drift-theorem-spelling TODO, and a CLAUDE.md long-cycle amendment; a live `main`-side cite dangles into it | branch `c3dc3986` | recorded |
| B-5 | `spec-parity` + s1…s6 — unmerged arc awaiting the user check-in (pre-merge audit ask + designation curation 44→48 + a consolidated 15-item agenda) | `TODO.md:391`, `:417` | **blocking** |
| B-6 | `spec-parity-s2` — parked RED (see P-4) | `TODO.md:749` | recorded |
| B-7 | `raft-w43`, `w32-5b`, `w32-qrows` — worktrees provisioned at `main`'s tip with **zero commits**: the next three arcs are staged but unstarted | `git worktree list` | recorded |
| B-8 | ~11 stale `worktree-agent-*` branches + ~20 retired arc branches never pruned | `git branch -a` | post-launch |
| B-9 | This lane (`audit-prep`) has no `artifacts/coverage/`, so a gate run here needs `GOLEAN_ALLOW_NO_DIFF=1` — correct by design, stated so a `note` is not misread | `scripts/coverage-baseline-diff` | recorded |

### §3.11 Coverage frontier, corpus and external instruments (16)

| # | item | where | relevance |
|---|---|---|---|
| C-1 | **15 FR rows / 84 claimed frontier reds**, enumerated in the ledger; raft-path: FR-5 (sync routing, queue TOP), FR-9 (imported named TypeDefs), FR-14 (stdlib, in aggregate). **§2 R-4 finds FR-5 and FR-8 have no red left** | `docs/language-coverage-ledger.md:311-362` | mixed; FR-5/9/14 **blocking** for raft |
| C-2 | 10 Q-row concurrency design questions / 21 reds, each with an owner, none queued | `docs/language-coverage-ledger.md:398-416` | post-launch |
| C-3 | 7 T-row sufficiency gaps (T-1, T-2, T-3 — a membership row BLOCKED on the E3/E4 decision, "do NOT pin strict" —, T-4, T-6, T-7; T-5 DONE) | `docs/language-coverage-ledger.md:427-433` | post-launch |
| C-4 | §5.1's five sequential features NOT queued, with written profound reasons (ratified 2026-08-20) | `docs/language-coverage-ledger.md:371-396` | recorded |
| C-5 | 34 coverage-ledger area rows — 23 `partial`, each naming its missing subareas in-line; a standing accounting backlog | `docs/coverage-ledger.md` | post-launch |
| C-6 | The 15 untriaged ids — 11 `coverage`, 4 `latitude`, **0 `wrong-answer`**. The `latitude` four retire ONLY by an envelope, never by a fix | `baselines/untriaged-ids` | recorded |
| C-7 | Ratchet-honesty note: `coverage` rose 7→11 on 2026-08-21 for ZERO new holes (four spellings of one class) | `baselines/untriaged-count` | recorded |
| C-8 | Mini-slices A3 (map multi-assign targets), A4 (chan type args — owes a reflect-spelling probe + a mangling-surface test update), A5 (shadow-capture tuple), A7 (multi-line panic payload — owes an edge enumeration proving the identity refusals still fire FIRST) | `docs/bugfix-arc-log.md:1200-1216` | post-launch |
| C-9 | **Mini-slice A6 — DEFERRED ON A FINDING; owns BUG-062; its scope as written is KNOWN-INCOMPLETE** and must be re-scoped per grossmith F-1 | `docs/bugfix-arc-log.md:2008-2014` | **blocking** |
| C-10 | grossmith F-2 — five corpus-ready probe rows (3 RED, 2 GREEN controls) plus three new red pins are OWED, guardrails-first | `TODO.md:819` | **blocking** |
| C-11 | **grossmith campaign 2 measured the PRE-W3.2 machine** and structurally could not reach pointers, channels, floats, goroutines, init or generics. **The re-run against the widened machine is owed, and so is the WIDTH-EXERCISING metamorphic formulation** — i.e. the lower bound is unmeasured on the current machine and the upper-bound instrument is unbuilt | `TODO.md:800-838` | **blocking** |
| C-12 | grossmith F-5 — hand back the observation that its STRICT lane's `order_witness` can land on unsequenced points | `TODO.md:822` | post-launch |
| C-13 | Six owed raft corpus rows, none landed: the twin as a corpus family; the perturbation schedules; the logger-teeth pair; a MEMBERSHIP row for the choice-stream twin; ok-tier trace replays; the D-12 refusal guardrail | `docs/raft-w42-log.md:589-599` | recorded |
| C-14 | Corpus hygiene owed: track frontend-blocked rows separately; promote `Corpus/challenges/semantic-edges/` one feature at a time; expand the negative-compile lane | `TODO.md:427-441` | post-launch |
| C-15 | Deferred until the foundation set: native interface dispatch; feature breadth up the raft ladder; `slices.Sort` extern + input fuzzing | `TODO.md:369-370` | recorded |
| C-16 | The tier=slow quick path's honest residual — it cannot see MACHINE-side envelope drift; deferred to the `--slow` cadence by design | `docs/2026-08-04_membership-lane-design.md:366-371` | recorded |

### §3.12 W7 — SpecTec-Go (7)

| # | item | where | relevance |
|---|---|---|---|
| S-1 | **Q12.2, the most consequential**: how SpecTec represents evaluation-order LATITUDE. Its backend runs latitude as a DETERMINISTIC pin, which would freeze all 13 K2 rows as fidelity claims — which doctrine forbids | `docs/2026-08-21_w7-desugar-inventory.md:3184-3208` | **blocking** for W7's target |
| S-2 | Q12.6 — does the certificate re-derive go/types or inherit it? **The differential CANNOT see a go/types inference bug** (shared fate with gc's types2) | same `:3250-3256` | recorded (a named TCB hole) |
| S-3 | Q12.5 — which side models memory layout; *"cheap to decide now, expensive to retrofit"* | same `:3243-3248` | recorded (time-sensitive) |
| S-4 | Q12.1 — wire-level vs AST-level simulation and stage 2; stage-3 shim re-entry has no answer in any of the three shapes | same `:3161-3182` | recorded |
| S-5 | Q12.3 — how the 35 shim rows are specified | same `:3210-3225` | recorded |
| S-6 | Q12.4 — where quarantine stubs sit in the spec's semantics | same `:3227-3241` | recorded |
| S-7 | The external tool was expected "within days of 2026-08-20"; the prep artifact (a 246-row desugar inventory) has landed | `docs/roadmap.md:367-408` | post-launch |

---

## §4 A PROPOSED AUDIT STRUCTURE — for Mike's scope-and-scale sign-off

This is a PROPOSAL. Per CLAUDE.md the ask is unconditional and the
scope is Mike's to set, trim or waive. Per the constitution the ask
itself is additionally constitutional here: *"the campaign may not start
without it having run."*

### §4.0 Four things to settle BEFORE the audit opens

The launch gate audits *"the INTEGRATED state as a composed claim chain,
at one settled tip"*. At `521f5b57` the tip is not settled and two
pieces of ground truth are missing.

1. **Decide what "the tip" is.** Three arcs are branch-complete awaiting
   merge sign-off (`holes-arc`, `raft-w42`, `w32-re-envelope`), and the
   constitution itself lives on a fourth unmerged branch 48 commits
   behind `main`. Auditing `main` as-is audits a state nobody intends to
   build on; auditing after they land requires four merge decisions
   first. **This is a sequencing ruling, and it is the first one.**
2. **Run one full `scripts/ci --diff` at that tip.** Every count in §1.1
   is read off the tracked BASELINE, not off a run — the branch's last
   gate used `GOLEAN_ALLOW_NO_DIFF=1`, legitimately, on a docs-only arc.
   "The record still matches the tree" is the one thing no reading
   establishes, and it is the cheapest single action that makes §1.1
   first-hand.
3. **Run `scripts/comparator-judge` once** (§3.8 K-4). The last
   independent kernel-replay certification is 371 commits old AND the
   statement TCB moved under it — three new `Expr` constructors and a
   change inside Challenge's trusted closure. The landmark trigger is
   scoped to designated-set/statement changes, so it never fired. An
   audit of the statement TCB that opens without this is auditing our own
   `Audit.lean` against itself.
4. **Attach `tools/reconcile-records --heavy` output** as the records
   dimension's starting point, so that reviewer spends its budget on
   whether the discrepancies MATTER rather than on finding them.

### §4.1 Shape

The standing pattern, unchanged: ground truth first (a real build,
`#print axioms`, the differential failing set — never prose) → parallel
DECORRELATED reviewers, one per dimension, skeptical persona, pointed at
PRIMARY SOURCES and explicitly **not** fed this dossier's conclusions →
every finding grounded to `file:line`, tagged verbatim-vs-reconstructed,
with what it could not verify → independent verification of each finding,
**defaulting to refute if thin** → honest synthesis, refuted findings
dropped, top survivors spot-checked by the operator.

**One deliberate deviation, and the reason for it.** Reviewers are given
§3 (the residuals register) but NOT §1's claims or §2's findings. §3 is
a *what is already known-open* list; withholding it wastes budget
re-deriving 148 rows. §1 and §2 are conclusions, and feeding conclusions
to a decorrelated reviewer is the thing the pattern exists to prevent.
The synthesis pass then asks the sharpest question this dossier can pose:
**what did nine reviewers find that §3 does not contain?**

### §4.2 Dimensions — 9 reviewers, Opus-class

| # | dimension | why it is sized this way | leads to hand it (NOT conclusions) |
|---|---|---|---|
| **D1** | **SEMANTICS — the interpreter as trust surface.** ALWAYS the primary dimension; never trimmed, never dropped because it has been passing | GoCore is both the differentially validated model and the statement language; proofs, specs and the differential all inherit its errors. BUG-002 was found by reasoning, not running | the four classes green gates cannot see, by name: unexercised paths, atomicity/granularity, fail-closed misclassification, claim strength |
| **D2** | **NONDETERMINISM-ENVELOPE FIDELITY** — each choice-consumption site's envelope argued against the Go SPEC TEXT | the too-wide direction **has no oracle**; review is the only check. And §2 R-1 found the reader-facing census is two sites behind the code, which is precisely a census of a different machine | the 9 `ChoiceSite` constructors; the six known-≠-gc deterministic points (E3, E5, E7, E13-assertion, R3-escaping, R15); the registry-granularity residual |
| **D3** | **STATEMENT ADEQUACY / ABOUTNESS** — what `SlowObs`/`obsOf?`, the readout corollaries and the agreement predicate actually project, against what the records' prose promises | the constitution's own governing ideology directs skepticism here explicitly: *"the observation notion is load-bearing … aboutness is the one thing no kernel checks"*. This dimension is NEW relative to prior audits and is the one the ideology asks for | `EnumSpec.lean`'s six-arm `obsOf?` (deadlock, fuel-out, stuck, unsupported all → `none`); the harness's S1–S4 checker; every "the theorem says" sentence in the raft logs |
| **D4** | **STATEMENT TCB + LAYERING** — designation, the walker, witnesses, the deletion test, first-order readouts | half the doctrine is mechanized and half is convention; §3.8 already has two live non-vacuity violations and the strongest new claim on the branch is undesignated | `proofs/Audit.lean`'s designated list; the ~80 gate lines that name a law rather than an instantiation; `checkCertM_slowObs`'s designation status |
| **D5** | **MACHINE → TWIN ADEQUACY** — the harness's scope statements against what upstream licenses, and against what the theorems will need | the whole raft claim rests here, nothing on this link is gated, and the ∀-choice-stream form the theorem needs has never been exercised | `deps/raft`'s `rawnode.go`/`node.go`/`doc.go`; `tools/raftsubject/twin-lib.go`; the D-1…D-12 subject-delta ledger; the §6 footprint checklist |
| **D6** | **THE INSTRUMENTS — do the gates compose honestly?** | the constitution's own bullet, and the class no single arc's audit can see. **Brief this reviewer explicitly: the question is "does a green gate MEAN what the records cite it for", NOT "can I get around a gate".** Escape-hunting against gates is out of scope by standing policy; gate-honesty-as-claim-honesty is in scope by constitutional requirement | the eight composition risks; the empty-input class; the four steps whose WARN is truncated out of view |
| **D7** | **THE RECORDS composing** | §2 mechanized part of this and found 10 + 19; the reviewer's job is which of them CHANGE A CLAIM, plus the ledgers §2 could not reach | give this one §2's output as its starting point (the stated exception) |
| **D8** | **OVER-SPECIALIZATION** — machinery shaped by raft rather than by Go | milestone pressure makes this the default drift, and the campaign is about to apply the most milestone pressure the project has seen | frontend special cases scoped to what raft calls; laws whose STATEMENTS encode target names; semantics fixes justified by corpus cases instead of Go probes |
| **D9** | **CAMPAIGN MACHINERY + CLAIM HONESTY** — is the constitution operative, are the continuity conventions provisioned, do the summary layers hold | the constitution is an unratified draft 48 commits behind `main` and unreferenced from it; §1.6 found the maxims' branch-state flags inverted in both directions; and every §2 discrepancy is in a summary layer, for the fifth records audit running | the constitution's §6 provenance pointers; `TODO.md`'s stale totals; `roadmap.md`'s 2026-07-19 banner |

### §4.3 Verification and synthesis

- **3 independent verifiers, Opus-class**, each taking a third of the
  pooled findings, **defaulting to REFUTE if the grounding is thin**.
  Verifiers do not see the reviewer's reasoning, only the claim and its
  cited `file:line`.
- **Operator synthesis**: drop refuted, spot-check the top survivors
  first-hand, and answer the dossier's own question — what is here that
  §3 does not contain?

### §4.4 Scale and cost

Measured, not guessed: this dossier's own five survey agents consumed
**206k–252k subagent tokens each** (avg ~230k) over 6–18 minutes. Audit
reviewers read more adversarially and verify against primary sources, so
budget the same order or somewhat more.

| | agents | est. tokens |
|---|---|---|
| reviewers (D1–D9) | 9 | ~2.2M |
| verifiers | 3 | ~0.6M |
| **total** | **12** | **~2.8M** |

Plus the three ground-truth runs of §4.0: a full `--diff` (hours,
wall-clock, unattended), `comparator-judge` (~5 min at the last
landmark, from a fresh clone), and `reconcile-records --heavy` (~1 min).

### §4.5 Trimming options, if the scale is wrong

Offered so a trim is a choice rather than an erosion. In the order the
dossier would give them up:

1. **Drop D8** (over-specialization) — the thinnest dimension at this
   tip, because very little target-specific machinery has landed yet;
   it becomes essential once the campaign is running.
2. **Fold D7 into D6** — both are "do the instruments say what they are
   cited for", and D7 already starts from mechanized output.
3. **Fold D9 into the operator's own pass** — it is largely
   record-hygiene, and §1.6 has already done the sweep.
4. **Cut verifiers 3 → 2.**

**What should not be trimmed, and why, stated plainly so the decision is
informed:** D1 is never trimmed (standing user direction). D2 and D3 are
the two dimensions with **no oracle behind them at all** — too-wide
envelopes and statement aboutness are checkable by review or by nothing.
D5 is the only review the raft claim will get before a theorem is hung
on it, since no gate touches that link.

# 2026-09-11 whole-project review — dispositions, decisions, the agreed sequence

[AGENT] coordinator, 2026-09-11. Records only: no fix, no baseline change,
no rule change. The review is `docs/2026-09-11_project-review.md` (landed on
main at `1ed23ae8` at the [USER]'s request). This note records how its
findings were filtered through the [USER]'s 2026-09-11 scope ruling, the
[USER] decisions taken on it the same day, and the next sequence the [USER]
agreed. Proposals here are [AGENT]; decisions are tagged.

**The scope ruling this note applies** ([USER] Mike, 2026-09-11, verbatim,
relayed by the [AGENT] coordinator — cite as relayed): «okay, I am still
concerned that we are not focusing our energy on actually making the *go
semantics* as good as possible. We don't have as of now a customer. Our job
is to make the Go seantics as good as we can make it. Nothing else. We can
do limited spikes to try to validate our choices, but our top level goal is
to make the semantics good. We should prioritize high value efforts, like
cleaning up the handling of state, and making the semantics structure
regular. We *can* provide a relational definition along with it too.
Everything else should be dropped». Earlier the same day: «We are not
building a reasoning system, that's for others to do».

## 1. Verdict on the review

Its measurements match the tracked state (3,665 baseline rows; one slow-tier
certificate; check-records clean). Its three new boundary findings are real:

- **F1** (file selection): the coordinator reproduced it independently on
  2026-09-11 — `main.go` + `extra_windows.go` with `func init() { x = 2 }`:
  `go run` prints 1, GoLean returns 2, clean export, no refusal.
- **F2** (module `go` directive): reproduced the same way — identical source
  under `go 1.21` vs `go 1.26`: Go 9 vs 3, GoLean 3 in both.
- **F3** (production decoder fail-open) is the 2026-09-05 gate audit's F9,
  ACCEPTED then (master plan §7.2) and still unfixed at `1ed23ae8`.

Its §16 roadmap, §8 and §15 are framed around a customer (a "generalizable
customer interface", a "sequential reasoning offer", a concurrent Iris
adapter, a customer pin) and were written against the pre-ruling master
plan. The roadmap is NOT adopted; the findings are dispositioned below.

## 2. Dispositions

| Review item | Disposition | Lands where |
|---|---|---|
| §4 F1 file selection | KEEP — wrong answer on trusted surface #1 | BUG-108; sequence step 1 |
| §4 F2 module `go` directive | KEEP — wrong answer on trusted surface #1; RULED [USER] refuse non-1.26 (§3) | BUG-109; step 1 |
| §4 F3 duplicate keys + `.getD .int` | KEEP — fail-open decoder (= 09-05 F9) | BUG-110; step 1 |
| §13 append cost (2,000 appends 4.5 s; 4,000 > 30 s) | KEEP — state-handling evidence; BUG-090's association-list diagnosis is stale (dense heap since A2) | BUG-090 re-diagnosis; step 2 |
| §9 detector access table separate from the heap | KEEP — confirms C1's access trace is the right cut | C1 design input; step 3 |
| §5 evaluation-order family (BUG-101/104) | KEEP — one model, not hoist patches (= 09-05 F6, design note still owed) | step 4 |
| §7 `recoverResult` inspects the continuation | KEEP — a structural irregularity | C3 design input |
| §9 `NPDRFReduction` false as written | KEEP — restate or delete; PENDING [USER] (§3) | its own design note before any lane |
| §7 "stated simulation contract" (init, labels, choices, memory effects, output, terminal) | KEEP — the relation's target statement, no customer language | the relational line (c) |
| §6 two contracts (portable language semantics vs gc target instance) + latitude gap list | KEEP — fits the weakest-machine doctrine | latitude inventory note; step 2 |
| §17 documentation volume | KEEP — already ruled: plans stay SHORT | standing |
| §16 step 3 sequential reasoning offer / customer interface | SET ASIDE — customer programme | — |
| §16 step 5 tail: concurrent Iris adapter, ownership example | SET ASIDE | — |
| §16 step 7 customer pin / release protocol | SET ASIDE | — |
| §8 typed-admission profile expansion for customers | SET ASIDE (invariants stating the relation's domain stay in scope under (c)) | — |
| §10 / §16 step 4 breadth programme (module loader, reflection, external effects, "almost any Go program") | SET ASIDE — coverage grows by the differential corpus, not a breadth target | — |
| §11 Cedar functional driver as acceptance | SET ASIDE — Cedar is a coverage subject only ([USER] 2026-09-11) | — |
| §15 "Customer utility" axis | SET ASIDE | — |

## 3. [USER] decisions, 2026-09-11 (verbatim, relayed)

1. **F2 policy** — «Yes, refuse non-1.26». → BUG-109's fix: a lowered
   directory (or an imported source package) whose `go.mod` `go` directive
   names a language version other than 1.26 is REFUSED by name at export.
   [AGENT] detail: a directory with no `go.mod` keeps the pinned 1.26 (the
   corpus's mode today — zero `go.mod` files under `Corpus/`; unchanged).
2. **`NPDRFReduction`** — «unsure right now, probably restate». → PENDING
   [USER]. No proof work starts against the current statement; a short
   design note poses restate-vs-delete with the observable-state shape
   (allocation renaming, `main` exit) before any lane.
3. **Worktrees/branches** — «keep the worktrees for potential future
   reference». → No pruning.
4. **The sequence** — «Agree on the sequence: make sure this is captured
   properly». → §4.
5. **Evaluation-order mechanism** (2026-09-16) — «I think the Cerberus model is the
   correct one». → an explicit `unseq` construct in the core; the v1 note's
   endpoint scheme retired; record and consequences in
   `docs/2026-08-31_qrow-rulings.md`, «The evaluation-order mechanism ruling
   record (2026-09-16)»; v2 lane `design/eval-order-model-v2-0916`.

## 4. The agreed sequence ([AGENT] proposed, [USER] agreed 2026-09-11)

1. **Now — fix lane BUG-108/109/110** (frontend + decoder, fail closed):
   red-first corpus rows first, BUG `Cases:` lines, `scripts/ci --diff`,
   audit ask. Exit: no accepted input silently changes its file set or
   language version; wire rejection tested through the real CLI.
2. **Now, in parallel, records only:** (i) re-diagnose BUG-090 with a
   profile on the review's append workload and retire the association-list
   explanation; (ii) a short two-contracts note with the review's latitude
   gap list (Platform = gcAmd64, no float fusion, append-capacity interval,
   zero-size pointer identity, scheduler boundaries) folded into
   `docs/2026-08-11_latitude-inventory.md`.
3. **Next — B7, then C1.** B7 re-briefed under the ruling: the 2026-09-06
   design's fixed-context/mutable-store split is reused, its typed-consumer
   -sprint framing dropped. C1 then carries the cost model from (2)(i) and
   the access trace that replaces `Race.lean`'s per-shape table.
4. **Design note before any lane:** the evaluation-order model (09-05 F6);
   BUG-101/104 are resolved inside it.

The ladder after C1 is unchanged (design-hygiene arc): P → C3 → C4 → B6.

## 5. What this note does not do

No fix lands here. BUG-108/109/110 are `Pinned-by: none` until step 1's
red-first rows exist. Master plan §8 points here; nothing else in the plan
is edited. Push is a separate sign-off.

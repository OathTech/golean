# TCB and proof-infrastructure layering (user directives 2026-08-01)

Two standing architectural requirements, recorded for the
proof-automation arc's CLOSE-OUT and binding on everything after
(especially the Raft-properties work). Persisted here so they survive
compaction and agent switches; both are audit dimensions from now on.

## 1. The TCB doctrine: Iris stays fully outside

**The core aim, stated as the DELETION TEST (user sharpening,
2026-08-01): top-level theorem statements must be SEMANTICALLY
INTERPRETABLE without Iris — if Iris were deleted from the build, the
statement must still elaborate and denote the same proposition in
base definitions. "We can still ask the question and have it mean
something."** This is stronger than human understandability and it is
FORMAL: the transitive DEFINITIONAL CLOSURE of the statement (every
constant its type unfolds through, by module of origin) must be
disjoint from Iris — not merely import-hygienic (a statement that
merely imports Iris unused survives deletion; one that unfolds through
any Iris-defined constant does not, however innocent it looks). Proofs
may use anything — Iris is a proof device behind the exit pipes, and
proofs are deleted with it; the theorems' STATEMENTS remain and must
still be the same questions.

Under the deletion test today: `execStmt`/`loadLoc`/`Steps`,
`HProp`/`sat`/`Heaplet` (our deep-embedded, Iris-free SL), and the
Surface judgments all survive; anything mentioning `IProp`, `WP`,
`iprop(...)`, invariant tokens, or ghost cameras does not.

The statement-dependency ladder, from best to acceptable:

1. **First-order readouts over the interpreter** (`execStmt` run ⇒
   `loadLoc` value — the `goldenReturnsTwo` /
   `quorumOneKnownReturnsTwelve` / `quorumThreeAllReturnsSix` shape):
   the gold standard. Every headline theorem SHOULD ship one.
2. **Surface judgments** (`GoTriple`/`GoSpec`/`GoFuncSpec*` over
   `HProp`/`sat`/heaplets): acceptable — the deep-embedded SL is small
   and self-contained — but it is already more than "base", so the
   readout corollary stays mandatory alongside it.
3. **Relation-quantified statements** (`Steps` — needed for
   invariance/mid-run properties, later for trace/refinement claims):
   acceptable when the property is genuinely about mid-run states;
   the machine relation joins the statement TCB, Iris still must not.

**For Raft:** ghost state, history variables, linearization points,
and prophecy-style machinery are PROOF devices. The moment one appears
in a top-level STATEMENT, the doctrine is violated — the statement
must be reformulated (trace properties over the machine relation;
first-order readouts where possible) before the theorem is claimed.

**Mechanization owed at close-out (not just discipline):**
- A per-theorem statement-TCB gate in `proofs/Audit.lean`: for each
  designated headline theorem, walk the TRANSITIVE constant closure of
  its TYPE (statement closure, not proof closure — unfold through
  definitions, exactly the deletion test) and FAIL the build if any
  constant's module of origin is an Iris module (module-of-origin, not
  namespace — the same discrimination the axiom sweep uses, so a
  stray top-level or renamed constant cannot dodge it). This turns the
  deletion test into a build error.
- Extend the surface-purity ci scan from its two-file list to the full
  set of statement-bearing modules (today `QuorumTargets`,
  `QuorumRefSpec`, `AutomationTargets` are Iris-free by import chain
  but UNGATED — found 2026-08-01, the exact silent-reopen class the
  gate's own 2026-07-23 hardening comment warns about).

### Operational enforcement: Comparator (noted by the user, 2026-08-01)

The Comparator tool (trustworthy Lean proof judge: a CHALLENGE module
with sorry-bodied theorem statements in a trusted import closure; a
SOLUTION judged from outside via lean4export + the Lean kernel and
optionally the independent nanoda kernel, landrun-sandboxed) is the
operational completion of this doctrine. Our in-build gates run INSIDE
the proof layer's elaboration environment — sufficient against honest
error, but agent-built proof trees could in principle compromise their
own checking environment (Comparator's "never previously compiled the
Solution" assumption names the hole). The mapping onto our
architecture is exact: Challenge = the deletion-test layer (the
statement-bearing Iris-free modules over GoCore base definitions —
the same designated-theorem list the statement-TCB gate certifies);
Solution = the entire proof tree, Iris and tactics included. Composed
trust: Challenge closure + kernel(s) — agents, Iris, go_walk, and the
elaboration environment all OUTSIDE the judge.

Integration (queued for close-out, binaries user-fetched like deps/):
build the Challenge module (falls out of the statement-TCB gate's
designated list); run at pre-merge/milestone cadence from a fresh
clone (the "never compiled the Solution" discipline — the fuzzer's
disposable-clone pattern); landrun + lean4export@4.31-compatible +
optionally nanoda in PATH; OPEN QUESTION to test empirically: whether
landrun/systemd-run nest inside the nono sandbox or Comparator runs
stay user-invoked outside the agent session.

## 2. The layering doctrine: general infra / target infra

**Ideal division of labor: (1) generalized proof infrastructure that
works for ANY GoLean proof; (2) target-specific (today: quorum/raft)
infrastructure that only USES the general layer.** The target layer
contains: pins, walks, per-program invariants, and instance theorems —
never laws, lifting cores, or tactics.

Current state (assessed 2026-08-01): the division mostly holds —
Lang/Ghost/Lifting/HeapBridge/Laws/*/Tactics/Surface* are general;
Specs/* is target — with known debt:
- `Laws/QuorumOps.lean` is misnamed/misplaced: its LAWS are general
  (the stmtOpK walk family, mapLookup, sortSlice) with quorum only in
  witnesses; the general laws belong in properly-named general
  modules, witnesses staying wherever their pinned programs live.
- Nothing ENFORCES the direction. Owed at close-out: an import-
  direction lint in ci (general modules — Laws/*, Lifting, Ghost,
  Tactics/* — must not import Specs/*; Tactics must not import GoCore
  semantics at all, which `GoWalk.lean` already satisfies by
  construction), plus a short layer map in `docs/architecture.md`.

## Close-out checklist (this arc)

1. Move general laws out of `QuorumOps.lean`; layer map documented.
2. Statement-TCB gate + widened surface-purity scan (above).
3. Both doctrines as named dimensions in the final pre-merge audit
   (alongside semantics / vacuity / over-specialization /
   gate-honesty): "is any top-level statement's meaning dependent on
   Iris or on target-specific machinery it shouldn't need?"

(Placement restored at the 2026-08-01 audit response: the Comparator
deferral below was inserted between items 2 and 3, orphaning item 3 —
the one CLAUDE.md-mandated unconditional close-out obligation — inside
a section headed DEFERRED, where CommonMark absorbed it into the
preceding paragraph. The insertion was mechanical, not a decision; the
audit ask was in fact made.)

## The Comparator sprint (DEFERRED post-merge — user decision 2026-08-01)

Comparator integration is its OWN short focused sprint after this
arc merges, not a close-out item: reify the statement-TCB gate's
designated-theorem list as the Challenge module (sorry-bodied, in the
gated Iris-free closure); wire the config + fresh-clone wrapper
script; validate the landrun/systemd-run invocation paths (an
UNSANDBOXED agent does the setup/mechanics portion — it has network
and can exercise systemd-run; the golean loop lands the tracked
artifacts). Prerequisites already in place: deps/comparator @ the
v4.31.0-toolchain commit fd2e25d, deps/lean4export built @ v4.31.0,
landrun installed (profile draft v1.5.0 grants $HOME/go/bin, pending
promote); remaining fetch: comparator's Lake deps (one outside-sandbox
`lake build`), optional nanoda.

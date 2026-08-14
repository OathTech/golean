# CLAUDE.md

Operating contract for work in this repo. This is the concise, always-loaded
version; `AGENTS.md` holds the architecture rules and
`docs/gocore-semantics-upgrade-goal.md` the deep operating guide. Read those
before nontrivial semantics work. Amend this file when a practice proves its
worth or its cost — keep it lean; it loads every session.

Goal: build a fast, careful Go-to-Lean verifier. North star target:
`etcd-io/raft` (`docs/roadmap.md`). Move aggressively; the practices below
exist because they let us do that without accumulating debt, not as ceremony.

## The two bounds — what we are building (2026-08-11, doctrine)

**A trustworthy, PORTABLE Go semantics** — the weakest machine Go can
plausibly ever do, exercising all degrees of freedom latent in the
language — never a model of one scheduler or of behavior already seen.
**Differential testing is the LOWER bound** (observed ∈ modeled — its
whole meaning is membership); **spec/memory-model/docs/the deployed-code
corpus argue the UPPER bound**. If a conforming implementation does
something the machine cannot, that is DEFINITIONALLY a bug (almost
always ours). Deterministic gc-pins of latitude are velocity
scaffolding carrying re-envelope obligations — never fidelity
achievements. Full doctrine + the simplifying-assumptions register:
`docs/2026-08-11_essence-of-go-doctrine.md`; the per-point census:
`docs/2026-08-11_latitude-inventory.md`.

## The validation gate (always, before any commit that touches runtime code)

0. **Run `scripts/ci`** — the one-command gate that bundles the steps below
   (escape-hatch preflight, core build, proofs build incl. the in-build `Audit`
   axiom/non-vacuity gate, eval tests, baseline diff of the last run). It fails
   loud and local. For runtime changes add the differential (step 2 / `--diff`).
   The individual steps, when you need them directly:
1. `lake build` passes — **as `scripts/capped lake build`, never bare** (below).
2. Run the focused differential slice for the touched area
   (`scripts/coverage run <ids...>` or `scripts/diff-one <id>`, native
   frontend), plus `lake exe gocore-eval-tests`.
3. Diff the failing case-id set against the last recorded baseline
   (`scripts/coverage-baseline-diff`). **Same set = no regression.** Any new red
   is investigated before committing. **No recorded run at all is a FAIL**, not
   a skip (2026-08-09): a killed `--diff` deletes the record up front, and
   "nothing has checked the corpus" used to exit PASS. A fresh clone therefore
   goes red until you run `scripts/ci --diff` once; an environment that never
   records one — CI's fast gate, or a fresh lane worktree on a docs-only arc
   where no runtime change owes a differential — sets `GOLEAN_ALLOW_NO_DIFF=1`
   explicitly and reports a visible `note` (scope widened 2026-08-12: the
   worktree-per-lane discipline makes fresh checkouts routine, and the audit
   flagged that the old text scoped the hatch to CI alone while docs-only
   lanes were already using it, correctly).

A green build is not evidence of correctness. The cheap, decisive signal is the
failing-set diff — it is what kept 13 consecutive cleanup slices at zero
regressions. The differential oracle is real Go (`go run`); the native Go
frontend (`tools/nativefrontend` + `NativeToIR.lean`) is the only frontend.

### Never run a Lean build uncapped (2026-08-09)

Every `lake`/`lean` invocation MUST go through **`scripts/capped`** (a rule,
not a description of the current state — see the uncapped list below), which
runs it in its own cgroup (`systemd-run --user --scope`, `MemoryMax` default
64G on a 125G box, `GOLEAN_MEM_MAX` to override, `=none` to opt out loudly).
On breach the kernel kills inside that cgroup only, so the build dies instead
of the machine. `scripts/ci` re-execs itself through it — a rule you can forget
is not a gate — so the gate needs no special handling; ad hoc builds do.
**The cap is a blast radius, not a budget:** use the heavy machine when a job
needs it, just never let one job take the box.

Why: a `by decide +kernel` in `compat/gobra` reached 60 GB in ~2 min and killed
the session twice; the OOM killer's badness score picks the multiplexer and the
agent quite happily. **The cause was a FALSE goal, not an expensive one** — a
fuel bug made the proposition false, so the kernel was grinding on something
unprovable; with the bug fixed the same line checks in 1.2 s. So the smell is
not "`decide +kernel` over `String`/`Char`" (the tokenizer kernel-reduces six
clauses in 558 ms) but **`decide`-family tactics on a proposition you have not
first evaluated**. Cheap habit that would have caught it in seconds: `#eval` the
`Bool` before asking the kernel to prove it — a decision procedure that must
reduce to `False` has no reason to terminate politely. When one does run away,
bisect it by layer under a small `GOLEAN_MEM_MAX` with a timeout; each probe
costs seconds. Two caps that DON'T work, measured, so nobody
"simplifies" the wrapper into one: `lean -M` is not enforced during kernel
reduction (audit-reproduced: under `-M 4096`, lean's own `VmRSS` was 4953 MiB
at t=10s and climbing, with no memory diagnostic), and `prlimit --as` kills
Lean above a threshold since it reserves address space per thread. RSS via
cgroup is the only honest knob.

Still uncapped, so treat with care: `scripts/coverage`, `diff-one`,
`comparator-judge`, `check-golden`, `check-imported-pins`, `test-import-goose`,
`test-lane-validation`, `comparator-setup`, `diff-coverage` when invoked
DIRECTLY (via `scripts/ci` they inherit the scope), and — the one most likely
to hit a pathological file — **the Lean language server**, which elaborates on
file open with no wrapper in the loop. CI keeps `GOLEAN_MEM_MAX=none` (no
systemd user bus on hosted runners) but the workflow wraps each gate step in
a SYSTEM-scope cgroup cap via passwordless sudo (2026-08-14): a runner VM
that dies uploads no logs and saves no cache, so "disposable, let it die" was
the wrong frame — `docs/2026-08-14_ci-runner-death-and-slow-tier-timeout.md`.

### Baseline pinning (the "recorded baseline" in step 3)

The recorded baseline is a **tracked** file, `baselines/native-full.tsv` —
`result<TAB>id<TAB>stage` per case, sorted by id, with a dated header (recording
commit, counts, frontend). `artifacts/` is gitignored, so a run's `latest.tsv`
is *not* the record; the tracked baseline is. `detail` (free-text errors) is
omitted on purpose — it churns; `result`+`stage` is the regression signal.

- **Diff a run against it:** `scripts/coverage-baseline-diff [results.tsv]`
  (defaults to `artifacts/coverage/latest.tsv`). Exit 0 = identical set (no
  regression); exit 1 prints exactly the drifted ids (PASS↔FAIL flips, stage
  changes, new/dropped ids). This *is* the step-3 gate, mechanized.
- **A `frontend-export` FAIL is an expected native-frontend coverage gap**, not a
  bug — but a *new* one still counts as drift and must be explained.
- **Re-pin the baseline only on a deliberate, explained coverage change** (a
  frontend/interpreter feature legitimately moves cases): regenerate the file
  from a full run, bump its dated header, and commit it *in the same change* that
  caused the move, with the reason. Never re-pin to launder an unexplained
  regression. A focused slice (`diff-one`/`coverage run <ids>`) is for the tight
  loop; the tracked baseline is re-pinned only from a **full** run.

## Capture decisions in files, not chat

Every relevant design decision, tradeoff, or open question must be written into
a tracked file (the goal/plan doc for the work, `TODO.md`, or a dated design
note) — not left in conversation. Chat is ephemeral; the repo is the record. If
a decision changes direction (e.g. reshaping GoCore, choosing a wire format,
deferring a feature), note what was decided, why, and what it affects. This is
what lets any session — human or agent — resume without re-deriving context.

Design principle for GoCore specifically: **GoCore is reshapeable, not
sacrosanct.** Judge its shape by two questions — does it support *reasoning*
(a clean relational/WP story) and does it help get *emission* right (frontends
lower to it cleanly)? If GoCore's shape fights either, change GoCore rather than
contort around it, and record the decision.

## Guardrails first: differential tests before tool buildout

Before building a feature of the tool (a frontend, a lowering path, a semantic
construct), add the differential corpus cases that pin its target behavior
first — isolated per feature, with edge cases. The Go oracle (`go run`) is free
and authoritative for the LOWER bound — at a forced point that is the whole
story; at a latitude point a case witnesses one member, never the envelope's
width (the two bounds above) — so writing the case first costs almost nothing
and fixes the target before the implementation can drift. A tool feature is
not "started" until its guardrail cases exist and classify correctly (a case
the tool can't yet handle should be visibly frontend/feature-blocked, never a
false pass).
This is why the corpus is frontend-independent: canonical Go is the input to
both `go run` and the tool. Aim for suites strong enough that *green implies the
target is covered* — see the three-layer sufficiency strategy in
`docs/native-frontend-goal.md` (isolated cases, edge enumeration, integration +
input fuzzing).

## Fail closed, always

Unknown wire nodes, unsupported features, malformed state → an explicit
`.unsupported` / error at the boundary. Never a silent approximation, never an
inert placeholder in dead code. Never count `unsupported`, `stuck`,
frontend-export failure, or a Lean internal error as a passing/conformant case.
A visible red case beats a hidden wrong answer.

## GoCore stays pure

GoCore contains only Go runtime semantics. Frontend-specific concerns (name
resolution, desugaring, any wire quirks) are quarantined in `NativeToIR` and
fail closed there — they never become GoCore nodes. Semantic identity is
`TypeId`/`FuncId`, never raw frontend strings.
Every mangling strip happens at exactly one boundary constructor and
collision-checks. This isolation is what lets the frontend be replaced without
touching the semantic core — protect it.

## Small slices, honest regressions

One semantic concern per commit. Validate each. When a cleanup intentionally
turns a case red (removing junk it depended on), record it: case id, old→new
stage, the bad assumption removed, the clean fix. Do not weaken the oracle,
skip a case, or edit canonical Go to make something pass.

## Proof-facing code is total; keep it that way

New relational/proof-facing definitions (the relation in `Machine.lean`, the surface layer) are
total — no `partial`, no `sorry`, no `native_decide`. The executable
interpreter's big-step cluster is ALSO total (arc `eval-totalization`,
2026-07-21 — GoCore has 0 `partial def`s; the remaining `partial`s are
frontend/CLI, outside the semantic core). Do not add new `partial` semantic
functions without a concrete reason, and prefer structural/well-founded
recursion in new code so the proof direction stays reachable. (Status line
corrected 2026-07-22 per pre-merge audit — the old text still called the
interpreter `partial`.)

**Non-vacuity gate (axiom-clean is not enough).** A WP/Hoare law can be
axiom-clean *and vacuous* — premises no real program can satisfy simultaneously,
so no instance exists (this bit `wp_assign`'s `hred`, twice: shipped, caught by
audit, then nearly re-shipped as `wp_deref_store`). So: **every user-facing
WP/Hoare law ships in the same commit with a discharge *witness*** — a theorem
that instantiates it on a concrete program and discharges every premise but the
genuinely-external ones (a store-typing side-condition is fine to leave). See
`wp_assign_lit`, `wp_index_get_witness`. No witness ⇒ the law is a scaffold; mark
it so in its docstring, and never let the docstring claim applicability the
witness doesn't demonstrate. A premise quantified `∀σ` over the *state* is the
smell to check first.

## Slices are for iteration, not the record

For the tight edit/test loop use focused ids or a curated smoke subset. Full
runs and handoff-quality claims require the full-run metadata, not a filtered
`latest.tsv`. For multi-session efforts, append to the persistent handoff
(`docs/gocore-semantics-upgrade-handoff.md`) in its stated format — but do not
impose that ceremony on a one-line fix.

## Branch, merge, and adversarial audit (before milestones)

Adopted from ACL2Lean (see `docs/2026-07-19_review-merge-practices.md` for the
full pattern; merge steps made exact 2026-07-20 after a pointer-surgery merge
(`git branch -f`) caused avoidable confusion — the protocol below is the ONLY
way an arc reaches `main`).

### The merge protocol — follow EXACTLY, every step, every time

1. **ALL work happens on a branch off `main`** — never directly on `main`,
   including doc-only and process-contract changes, unless the user directly
   authorizes a specific commit to land on `main` (rule tightened 2026-07-21
   at user direction; the old "process amendments may land directly" carve-out
   is revoked).
2. **Arc complete → run the gate:** `scripts/ci` (add `--diff` when runtime
   code changed; use `--slow` instead when the arc touched a `tier=slow`
   row, its certified-set record, the enumerator, or the interpreter —
   the cached membership path defers full envelope re-certification to
   exactly this flag, and the nightly CI schedule runs it; tiered-checking
   design 2026-08-08). Must be green before anything else. If the arc added or
   changed a designated headline theorem statement (the statement-TCB
   gate's list), also run `scripts/comparator-judge` — the independent
   kernel-replay judge (landmark cadence only, never part of `scripts/ci`;
   comparator-judge sprint 2026-08-02).
3. **THE AUDIT CHECK — NEVER, EVER SKIPPED.** Before any merge, explicitly ask
   the user about a pre-merge adversarial audit: propose scope + scale
   (dimensions, agent count, model, cost) and get sign-off on that plan before
   launching any subagent. The user may **waive or trim** the audit — that is
   their call to make, never ours — but the *ask itself is unconditional*. No
   green gate, no prior audit of an earlier state, no urgency, and no "it's
   only docs" reasoning ever substitutes for asking. If an audit runs: findings
   are fixed on the branch, then re-run step 2. **Audit-response commits**
   get a focused DELTA-REVIEW of their own diff when substantive —
   especially when they touch gates/lints/trust surface; purely schematic
   fixes (doc corrections, pre-verified mechanical edits) may be waived
   from it (user policy 2026-08-01, resolving the final-state-vs-fixes
   tension explicitly).
4. **Pause, report, ask for merge sign-off.** Merge only on explicit approval
   given *at that moment, for that specific merge*. Approval is never inferred
   from an earlier "merge it", a green gate, a passed audit, or any broad "go
   ahead".
5. **The merge is exactly:**
   ```
   git checkout main
   git merge --ff-only <branch>
   ```
   If `--ff-only` refuses (main moved), rebase the branch onto `main`, re-run
   step 2, and return to step 4. No merge commits, no `git branch -f`, no
   pointer surgery — the operation must be legible as a merge to a human
   reading the terminal and the reflog.
6. **End state: checked out on `main`**, at the merged tip, tree clean, gate
   green. The next arc is decided from here and starts with
   `git checkout -b <new-branch>`. Do not linger on the merged feature branch.
7. **`git push` is a separate action** with its own explicit sign-off — never
   bundled into the merge, never assumed from it.

### How to run the audit (the pattern behind step 3)

- **Reviewer model: Opus** — pre-merge audit reviewers and their verifiers run
  on Opus-class models (user direction 2026-07-21); don't silently downgrade.
  **Worker model: Fable** — delegated workers on complex tasks (proof slices,
  semantics/tactic work) run on Fable (user direction 2026-08-01; both model
  rules encode the 2026-08 landscape — revisit on new model releases rather
  than applying blindly).
- **THE SEMANTICS IS THE PRIMARY DIMENSION — always audit it** (user
  direction 2026-07-24). GoCore's interpreter (`stepFn`/`execStmt`) is the
  trust surface everything else rests on: it is both the differentially
  validated model and the statement language (sem-adequacy framing,
  2026-08-03); proofs, specs, and the differential all inherit its errors.
  The Prop-level relation is proof infrastructure verified against it —
  audit their CORRESPONDENCE (a divergence is a proof-layer bug), not the
  relation as an independent authority. Do NOT reason "semantic dimensions returned zero
  findings, so semantics is low-risk" — that is dropping a check because it
  passes, and the worst defect this project has had (BUG-002, expression-step
  atomicity) was a semantics defect **no test could catch**, found by
  reasoning about the model and paid for with the whole reshape. Classes the
  green gates structurally CANNOT see:
  - **unexercised paths** — the differential validates only what the corpus
    runs (this is how Goose's break-in-switch divergence survived; found by
    reading, not running). Findings become corpus cases.
  - **atomicity / granularity** — step decomposition is unobservable
    sequentially and only bites under concurrency (the granularity ledger,
    `docs/2026-07-23_reshape-r1r2-machine-design.md` §1). BUG-002's class.
  - **fail-closed classification** — an `unsupported` that should have been
    a supported-and-correct answer never appears as a failure anywhere.
  - **claim strength / vacuity** — whether a law says what it appears to.
  - **nondeterminism-envelope fidelity** (2026-08-04,
    `docs/2026-08-04_nondeterminism-doctrine.md`) — each choice-consumption
    site's envelope argued against the Go SPEC TEXT: the too-wide direction
    has no oracle (go run cannot exhibit a behavior it never has), so
    review is the only check; too-narrow breaks theorem transfer and is
    the membership lane's job.
  - **statement TCB + layering** (user direction 2026-08-01,
    `docs/2026-08-01_tcb-and-layering-doctrine.md`) — top-level
    theorem STATEMENTS must be understandable from base definitions
    over the interpreter (Iris and 'fancy' theorems are proof devices,
    never statement dependencies; headline theorems ship first-order
    readout corollaries), and general proof infrastructure must stay
    cleanly separated from target-specific infrastructure.
  - **over-specialization** (user direction 2026-07-31) — machinery
    shaped by the current TARGET rather than by Go: semantics fixes
    justified by corpus cases instead of Go probes, laws whose
    statements (not witnesses) encode target names/values/fragments,
    frontend special cases scoped to what the target calls rather than
    to a language capability. Milestone pressure makes this the
    default drift; audit for it explicitly.
  Secondary but audit-only: **gate honesty** — do commits/notes/re-pin
  reasons match the code, did a gate quietly fail open (the 2026-07-23
  purity-scan rename hole was invisible to eleven green steps).
  Cadence is unchanged: pre-merge only.
- **Audit adversarially *before* claiming a milestone or merging, not after** —
  self-certification is unreliable, so audit before building a mountain on it.
  Audit the branch's **final state**: an audit of an earlier snapshot does not
  cover work added since (this bit us — "audited twice" was true of an old
  tip). The pattern (encode as a `Workflow`): (1) ground-truth first —
  real build + `#print axioms`/differential failing-set, never prose; (2)
  parallel *decorrelated* adversarial reviewers, one per dimension, skeptical
  persona ("probably subtly wrong — find where"), pointed at primary sources,
  not fed our conclusions; (3) every finding grounded to `file:line`, tagged
  verbatim-vs-reconstructed, with what it could not verify; (4) independent
  verification of each finding, defaulting to *refute* if thin; (5) honest
  synthesis — drop refuted, spot-check the top survivors yourself.

## Worktree-per-lane discipline (2026-08-10, user-directed)

Arc and lane work happens in **worktrees**, one per lane, under
`.claude/worktrees/<lane>` (branch named for the lane); the **primary
checkout stays parked on `main`**, where the operator coordinates
landings. Validated experimentally before adoption (§8b of the Verdi
compat note: two full gates beside mainline, zero interference;
~1 GB/lane of build dirs). The rules that make it safe:

- **Disjoint ownership for CONCURRENT lanes.** One lane at a time owns
  the semantic core + `Corpus/` + `baselines/` (re-pins and certified
  records do not merge textually); parallel lanes own disjoint trees
  (e.g. `compat/**`, docs-only scoping). Overlapping arcs run
  SEQUENTIALLY — worktrees isolate builds, not intent.
- **Cap budget:** two 64 G-capped builds can over-commit the 125 G box —
  parallel lanes set `GOLEAN_MEM_MAX=48G` or stagger full gates
  (arc-boundary events; staggering is nearly free).
- **Each worktree bootstraps its own `deps/`** with `scripts/setup-deps`
  (offline via `--from <sibling>`; pins table in the script, fail
  closed). The verbatim gate fails closed without it — by design.
- Landing is the unchanged merge protocol (rebase → gate → audit-ask →
  ff-only), operator-coordinated; `main` is the one serialized resource.
  Crash rule per lane: snapshot dirty worktrees to `refs/snapshots/`
  before any checkout/rebase touches them. Prune retired worktrees.

## Reference checkouts (`deps/`, in-repo and gitignored)

Checkouts available for reading — consult them instead of guessing or
web-searching when a design question has prior art. Moved from the old
sibling `../deps/` into the gitignored in-repo `deps/` (2026-07-30, so
the sandbox profile's workdir grant covers them; clone them yourself —
they are not tracked):

- `deps/goose` — goose-lang/goose, the Go→Rocq translator. `goose.go` is the
  whole translation (statement/expression handlers); `testdata/` is its
  supported-subset corpus.
- `deps/perennial` — the Rocq/Iris side. `new/golang/defn/*.v` is the Go
  model of record (`exception.v` = the return/break/continue "exception monad",
  `defer.v` = `wrap_defer`, `loop.v`, `chan.v`); `src/goose_lang/lang.v` is
  GooseLang itself.
- `deps/iris-lean` — the Lean Iris port we build against (also a Lake dep;
  keep the reading copy at the manifest's pinned rev).
- `deps/raft` — etcd-io/raft, the north-star target (REQUIRED for the
  quorum-pilot arc).
- `deps/verdi` @ `7e1641b`, `deps/verdi-raft` @ `a3375e8`, `deps/StructTact`
  @ `97268e1` — the Verdi system model (`theories/Core/Net.v`) and its Raft
  instance: the spec `compat/verdi` ports, so the primary source for any
  fidelity question (`docs/2026-08-09_verdi-compat-layer.md` §1).
- `deps/rocq-lean-import` @ `96686c4`, `deps/lf-lean` @ `2c0d52e` — the public
  half of the Lean↔Rocq kernel-import correspondence path: the plugin (older
  text export format, pinned lean4export `c9f8373`) and 1,276 worked iso
  examples. Read before any certification-toolchain work (§3 of the same note).
- `deps/grossmith` — the seed-deterministic differential conformance
  GENERATOR for Go programs (external project; hands findings over as
  dated docs, e.g. `docs/2026-08-07_grossmith-findings.md`). Supersedes
  the retired `side/gofuzz` prototype (founding record:
  `docs/2026-08-01_go-fuzzer-side-project-brief.md`).
- `deps/gobra`, `deps/aeneas`, `deps/strata` — other verification
  toolchains kept for comparison.

Design comparisons against Goose/Perennial are recorded in the arc's design
note (e.g. `docs/2026-07-24_sequential-coverage-scoping.md` §5), not left in
chat — including where we deliberately diverge.

## Housekeeping

- `.claude/` is gitignored. Date working notes `YYYY-MM-DD_name.md`; top-level
  docs (README, roadmap, this file) are exempt.
- Sandbox/scratch conventions: `docs/agent-sandbox.md`. For ad hoc Go probes set
  `GOCACHE="$PWD/artifacts/go-build-cache"` (repo-local, sandbox-writable) or
  `GOCACHE="$TMPDIR/go-build"` — **not** `/private/tmp/...`, which the command
  sandbox denies. The differential scripts already set their own repo-local cache.
- Do not `rm -rf` scratch dirs without approval; leave them for OS cleanup.
- **Diagnosing async results before calling them "failed":** a background
  `Bash`/`Workflow` that buffers can show empty stdout mid-run — check the
  artifact it writes (a TSV, the task `result`), not stdout. A Workflow
  `<failures>` line is a **single branch** failing (e.g. one agent's
  StructuredOutput retry cap), not the run; read `<transcriptDir>/journal.jsonl`
  (one result per agent) and `<usage>` (`agents_error` vs `agents_done`) before
  reporting failure. Say what survived. (Recorded because this misfired twice.)

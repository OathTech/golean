# Comparator judge sprint — plan of record (2026-08-02)

Goal (user decision 2026-08-01, post proof-automation merge): a short, focused
sprint that stands up **Comparator** (`deps/comparator`) as an independent,
kernel-level judge for our designated headline theorems — the operational
enforcement of the deletion-test doctrine
(`docs/2026-08-01_tcb-and-layering-doctrine.md`). Comparator independently
re-checks, from export files replayed into the kernel: (1) the Solution proves
the *same statement* as the trusted Challenge, (2) axiom usage is within the
permitted set, (3) the kernel accepts — with the trust boundary being the
**import closure of the Challenge module**, not our proof code, our
`Audit.lean` pins, or Lake's incremental state.

## Standing rule (user direction 2026-08-02, recorded in agent memory too)

**Trust-establishing tools are never modified** — not Comparator, not
lean4export, not landrun, not any kernel checker; not by source patches
(however small or verified), not by wrapper shims in their invocation path,
not by unapproved binary swaps. When one misbehaves, suspect version skew or
our own invocation first; bisect versions in scratch; resolve by a **version
pin chosen with the user**. This rule exists because during setup a real
incompatibility was initially "fixed" by a one-line patch to Comparator —
reverted on user direction; the true cause was a landrun version skew (below).

## Environment: validated end-to-end (2026-08-02)

Every component pristine upstream; all verification against Comparator's own
test projects (`simple_match` accepted / `simple_mismatch` rejected with the
correct reason), invoked exactly as its README prescribes:

- `deps/comparator` @ `fd2e25d`, toolchain `leanprover/lean4:v4.31.0` — same
  toolchain as golean core and proofs. Built clean with its own lockfile
  (lean4export @ `8554815`, Lean4Checker @ `b739819`).
- **landrun: the version-skew finding.** Comparator relies on landrun passing
  an inner `--` through to lean4export (`landrun <flags> lean4export <module>
  -- <decls…>`). landrun's urfave/cli v2→v3 upgrade (commit `e53db14`,
  2026-01-27, first released in v0.1.16 on **2026-07-22**) makes the parser
  consume that separator — lean4export then reads theorem names as module
  names (`unknown module prefix`). The v0.1.15 *tag* is broken the other way
  (its `-ldd` misses the ELF-interpreter line of ldd output, so sandboxed
  exec of dynamic binaries fails EACCES). The working window is cli-v2-era
  main after the ldd fix. **Pinned (user-approved, user-run install):**
  `github.com/zouuup/landrun@5283024a2f49b28046c3b4a06d7d775c058d4d80`
  (pseudo-version `v0.1.16-0.20260127195639-5283024a2f49`) at
  `~/go/bin/landrun`. NB it self-reports "0.1.15" — identify it with
  `go version -m`, not `--version`. Prior 0.1.17 kept at
  `~/go/bin/landrun-0.1.17.bak`. Upstream report: Mike's call.
- **Works inside the nono sandbox** (profile `claude-local` v1.5.0, already
  promoted): nested Landlock composes (nono outer domain ∩ landrun inner
  domain); both smoke directions verified in-sandbox. No profile change
  needed.
- **systemd-run guard**: verified working from outside the sandbox AND from
  inside — the latter because Landlock on this kernel (6.8, ABI v4) cannot
  restrict pathname-socket `connect()`, so the user session bus is reachable
  from any sandbox; the spawned unit carries the README's exact
  `RestrictAddressFamilies=~AF_UNIX` confinement either way. (Flagged to the
  user as a general nono-containment fact; unfixable at the policy layer
  before kernel support.)

## Design decisions

### The judge project (`judge/`, tracked)

A small Lake project in-repo:

- `lakefile.toml`: requires `GoLean` (path `..`) and `golean-proofs` (path
  `../proofs`); two libs, `Challenge` and `Solution`. Toolchain v4.31.0.
- `Challenge.lean` — **the trusted artifact**. Sorry-bodied restatements of
  the designated headline theorems (the statement-TCB gate's list in
  `proofs/Audit.lean`, 23 at time of writing). Imports ONLY Iris-free modules
  (see the hoist below). Its import closure — GoLean core + the Iris-free
  statement modules — *is* the thing a skeptic must read, and it is exactly
  the TCB the doctrine already claims.
- `Solution.lean` — imports `GoLeanProofs`, restates each theorem with the
  same name, proves by direct reference to the real proof. Comparator then
  enforces statement-identity, the axiom allowlist (`propext`, `Quot.sound`,
  `Classical.choice`), and kernel acceptance.
- `config.json` — `challenge_module`/`solution_module`/`theorem_names` (the
  designated list)/`permitted_axioms`.

Drift note: if a Surface statement changes, `Solution.lean` fails to
elaborate at the next judge run (the by-reference proof no longer typechecks
against the restated statement) — caught at judge time, which is acceptable
at landmark cadence. The `theorem_names` list must be kept in lockstep with
`Audit.lean`'s designated list; the wrapper cross-checks the two and fails
closed on mismatch.

### The Iris-free hoist (prerequisite refactor, main proofs package)

Comparator's trust boundary is the Challenge **import closure**, so the
statement-bearing definitions must live in modules whose transitive imports
never touch `Iris.*`. Measured state (import-closure walk, 2026-08-02):

| module | closure |
|---|---|
| `GoLeanProofs.Surface` | clean |
| `Specs.QuorumTargets`, `Specs.QuorumRefSpec` | clean |
| `Specs.GoldenTargets`, `Specs.GoldenProgram` | clean |
| `Specs.GoldenQuorumPin` | **reaches Iris** (via `Laws.StmtOps`/`Range`/`Call` imports; its own pin defs are Iris-free) |
| `Specs.AutomationTargets` | **reaches Iris** (via `GoldenQuorumWP`, `Laws.Range`; its statement defs — `EncodesConfig`, `EncodesAcked`, `configPre`, the `_statement` props, the entry pins — are Iris-free) |

Hoist: split the Iris-free statement-bearing declarations of those two
modules into new modules that import only the clean chain (e.g.
`Specs/QuorumPin.lean`, `Specs/AutomationStatements.lean`); the originals
import the new modules. No statement changes, no proof changes — a module
split. Slice 2 first mechanically derives the exact constant→module map with
a `#eval` mirroring the statement-TCB gate's walk (constants per designated
statement, tagged with module of origin), so the hoist is driven by measured
data, not eyeballing. This is also doctrinally right on its own: the doctrine
says statements live below the Iris line; after the hoist, *module structure*
says it too.

### Cadence: a landmark gate, not an iteration gate (user direction 2026-08-02)

Comparator runs are expensive (full proofs build + two sandboxed builds + two
full-closure exports + kernel replay) and independent of the tight loop. So:

- **NOT part of `scripts/ci`.** The in-build gates (Audit axioms,
  statement-TCB walk, non-vacuity) remain the every-commit line of defense.
- **Run at landmarks**: before merging any arc that adds or changes a
  designated headline theorem statement, and before any external claim about
  a headline result. The merge-protocol audit ask for such arcs should note
  whether the judge was run.
- Invocation is user-visible and deliberate: `scripts/comparator-judge`
  (prints the systemd-run line it executes, verdict, and timing). Slice 4
  records the measured cost here.

### Sandbox interaction

Comparator's landrun sandbox grants write only to the judged project's
`.lake`. Path deps (GoLean core, GoLeanProofs) build into their own `.lake`
dirs, which are read-only in-sandbox — so the wrapper **pre-builds both
packages first** (they are our trusted code; comparator's sandbox is
defense-in-depth for adversarial Solutions, which ours are not). If Lake
still insists on writing into dep dirs in-sandbox, that surfaces as a loud
landrun denial at judge time — never widen comparator's own sandbox args (see
the standing rule); reshape the judge project instead and record it.

## Slices

1. **Plan + setup record** (this commit) — the version-pin finding, the
   standing rule, in-sandbox validation results.
2. **The hoist** — constant→module map via `#eval`, split
   `GoldenQuorumPin`/`AutomationTargets`, full `scripts/ci` (proof layer
   touched; no runtime code, so no differential).
3. **The judge project** — `judge/` as designed above; Challenge
   import-closure Iris-freedom checked mechanically (same walk the gate
   uses).
4. **First real run** — `scripts/comparator-judge`, record verdict + cost
   here and in the doctrine doc's Comparator section; mark the doctrine's
   "operational enforcement" section as live.
5. **Close-out** — cross-link cadence policy into the doctrine doc, CLAUDE.md
   one-liner if warranted, pre-merge audit ask (protocol step 3), merge on
   sign-off.

## Build log

- **Slice 2 (the hoist) — DONE 2026-08-02.** The measured map (a `#eval`
  mirroring the statement-TCB gate's walk, grouped by module of origin)
  replaced the plan's guess: `GoldenQuorumPin` needed NOTHING (its pins are
  proof-side, not statement-side) and the pinned-program module
  `Specs/GoldenQuorum` was already clean; the real hoist set was 22 defs
  across FIVE Iris-reaching modules (`GoldenQuorumWP` 8, `AutomationTargets`
  9 incl. the `NotTwelve`/`NotEleven` unproven-twin targets kept with their
  families, `GoldenQuorumAll` 2, `GoldenQuorumThree` 1, `GoldenRecover` 3).
  (Counts corrected at the pre-merge audit: the move is **24 defs** — the
  22 measured statement constants plus the 2 unproven-twin `_statement`
  targets — with per-module breakdown WP 9 / AutomationTargets 9 / All 2 /
  Three 1 / Recover 3; the original text said 22 and a breakdown summing
  to 23.) All moved verbatim (docstrings included; positional phrases like "below"
  corrected to file references — recorded, not silent) into the new
  `Specs/Statements.lean`, import closure 9 modules, measured clean. After
  the move the partition is exact: every statement-referenced constant is
  either in a clean module or IS one of the 23 designated theorems (which
  the Challenge restates, never imports). Gate changes, justified:
  `Statements.lean` registered in the surface-purity scan (clean-chain
  allowlist); `AutomationTargets`' pinned import list gained
  `Specs.Statements` and its "mixed by design" rationale was updated;
  `check_surface_imports` now strips comments before matching (same
  blindness class as the b27e608→3c1b4bf closure-walk fix — a docstring
  line starting "import closure…" false-positived; noisy, not fail-open).
  Full `scripts/ci` PASS, zero baseline drift (873/873).

- **Slices 3 + 4 (the judge pair + first real run) — DONE 2026-08-02.**
  Design revision, recorded: the planned separate `judge/` Lake workspace
  would need its own network fetch of the iris dep (sandbox-hostile, and a
  second copy to keep pinned); instead `Challenge`/`Solution` are extra
  libs of the EXISTING proofs package (never default targets — `lake
  build` doesn't touch them; the trusted lakefile is `proofs/lakefile.toml`
  itself). Challenge (23 sorry-bodied theorems, `Judge.*` namespace to
  avoid colliding with the real names in Solution's environment) imports
  only `Specs.Statements` + `Specs.GoldenTargets` — closure measured
  Iris-free. Solution restates each statement verbatim and proves by
  reference; it builds with ZERO sorries, which is itself the transcription
  check (every restated type accepted the real proof term). Statements the
  repo phrases via `_statement` defs use the same defs; readouts are
  written out in full — the best artifact for a skeptic. Gate exemptions,
  justified and documented in-line: Challenge alone exempt from the
  escape-hatch sorry-scan (its sorries are its function; Comparator
  re-elaborates it authoritatively); Challenge+Solution on the audit-
  coverage standalone allowlist (outside the audited build BY DESIGN —
  the judge's own axiom check + kernel replay is the stronger,
  independent check; the preflight still scans Solution's text).
  `scripts/comparator-judge` fail-closes on: comparator rev+pristine tree,
  landrun module pseudo-version, lean4export built, designated-list
  lockstep (short-name set diff vs `Audit.lean`), Challenge-closure
  Iris-freedom (transitive walk) — then runs the guarded invocation.
  **First run: PASS, all 23 theorems certified in 69 s** (warm proofs
  build; the sandboxed steps were Challenge elaborate+export, Solution
  elaborate+export, kernel replay), from INSIDE the nono sandbox, under
  `systemd-run` with `RestrictAddressFamilies=~AF_UNIX`. Full `scripts/ci`
  PASS after the exemptions, 873/873 baseline unchanged.

- **Slice 4b (fresh-clone discipline) — DONE 2026-08-02, user catch.** The
  first run judged the WARM `proofs/.lake` — the exact state comparator's
  assumption 2 ("never previously compiled the Solution") exists to
  exclude: stale or crafted incremental artifacts could poison the
  CHALLENGE's elaboration, and our working `.lake` is written by ordinary
  agent-driven builds. Standard practice made the wrapper's DEFAULT: clone
  the repo at committed HEAD into `artifacts/judge/clone-<rev>`, seed only
  the Lake dependency packages (network-free `lake update` reproduction —
  feeds nothing trusted: Challenge's closure contains no fetched dep, and
  the packages serve the untrusted Solution side, which the kernel replay
  re-checks), pre-build the pair ourselves (the README's blessed
  "pre-built `.lake` obtained without compromising your checking
  environment" — also what makes our layered packages fit comparator's
  proofs/.lake-only write grant), then run the guarded judge: Challenge is
  exported BEFORE Solution is touched, and the sandboxed builds are
  no-ops. Clone removed on success, kept for inspection on failure.
  `--in-place` keeps the warm-tree run for iteration, verdict-labelled
  NOT authoritative. **Measured authoritative cost (post-audit flow,
  trusted-side-only pre-build): ~2 min wall** — clone + seed + Challenge
  pre-build ≈ 50 s, judged phase 69 s (comparator's sandboxed cold
  Solution build + both exports + kernel replay). PASS 23/23 at
  `3ba989d31aa6`, from inside the nono sandbox. (The first-iteration flow
  measured 88 s but pre-built the Solution unsandboxed — retired at the
  audit, finding 2.)

## Pre-merge audit + response (2026-08-02)

Two decorrelated Opus reviewers (proof/statement side; gate/tooling side,
user-trimmed from six) + one refute-by-default Opus verifier per deduped
finding, over final state `3ba989d`: **14 findings raised, 12 confirmed, 2
refuted.** Hoist fidelity, Challenge faithfulness (each `Judge.*` statement
vs the real theorem), and the three `scripts/ci` gate edits survived
scrutiny; every confirmed finding was in the NEW wrapper/docs, majors
first:

1. **[major] The wrapper's closure walk re-introduced the retired
   fail-open `^import` anchor, and `Challenge.lean` was in NO `scripts/ci`
   scan** — an indented/`public` import of Iris into Challenge would have
   passed both gates while Challenge.lean claimed otherwise. FIXED: the
   canonical matcher + comment stripper now live once in
   `scripts/lean-scan.sh`, sourced by both `scripts/ci` and the wrapper
   (ends the drift class); the wrapper walk uses `lean_imports` and FAILS
   on unknown module roots instead of skipping; `scripts/ci` now pins
   `Challenge.lean`'s direct imports to exactly the two clean statement
   modules. Probe recorded: an indented `import Iris.ProofMode` is now
   seen; commented phantoms are dropped.
2. **[major→doc] "Challenge exported before Solution is touched" was false
   of the fresh-clone flow**: the pre-build compiled Solution unsandboxed
   in the shared `.lake` BEFORE comparator ran — precisely assumption 2,
   which the docs claimed was now structural. FIXED structurally: the
   pre-build covers ONLY the trusted side (`lake build Challenge` — core +
   clean chain, the README's blessed pre-built path and the reason the
   layered write-grant works); the untrusted Solution is elaborated
   exclusively inside comparator's landrun sandbox, after the Challenge
   export has already been taken.
3. **[minor] Preflight checks read the working tree while the judge ran
   the HEAD clone.** FIXED: all artifact checks (config, lockstep, closure
   walk) run against `CHECK_ROOT` = the judged tree.
4. **[minor] `judge-config.json`'s `challenge_module`/`solution_module`/
   `permitted_axioms` were unvalidated.** FIXED: pinned in the wrapper
   (an axiom-set widening must edit the script, visibly). The fix's own
   first run fail-closed on a sed-range bug in the new check
   (`/start/,/end/` swallowing to EOF) — corrected to single-bracket
   extraction; recorded because the failure was the check working.
5. **[minor] lean4export's rev was never checked; binaries live outside
   the pristine check.** FIXED: lean4export package pinned by rev + clean
   tree; the binaries-are-built-artifacts residual trust is now stated
   honestly in the script header (rebuild via `comparator-setup` if in
   doubt).
6. **[note] Lockstep compared flattened short names with no collision
   guard.** FIXED: duplicate short names across designated namespaces now
   fail the run.
7. **[note ×3] Doc corrections**: hoist counts (24 = 22 measured + 2
   twins; WP 9/AT 9/All 2/Three 1/Recover 3), the "same walk as the
   statement-TCB gate" overclaim, and the assumption-2 claims — all
   corrected in place above.

Refuted (recorded): a claimed weaker-restatement hole in the `Judge.*`
scheme (Solution's by-reference proofs ARE the mechanical tie), and a
claimed fail-open in `strip_lean_comments` for unbalanced `/-` (it
over-flags, fail-closed).

## Exit criteria — all MET 2026-08-02 (close-out)

- All designated theorems pass the judge end-to-end on this machine with
  every trust component at a pristine, recorded version (comparator
  `fd2e25d`, lean4export `8554815`, landrun `5283024a2f49`) — **MET**
  (23/23 certified in 69 s warm, from inside the nono sandbox, under the
  systemd-run guard).
- Challenge's import closure is measured Iris-free — **MET**, wording
  corrected at the pre-merge audit: the wrapper runs a MODULE-level import
  walk (hardened post-audit: canonical comment-stripped tolerant
  extraction, unknown roots fail), which is deliberately weaker than the
  statement-TCB gate's constant-level walk in `Audit.lean` — that gate
  remains the in-build authority; the wrapper's walk is judge-side defense
  in depth, and `scripts/ci` now pins `Challenge.lean`'s direct imports
  too.
- Cost of a judge run is measured and recorded; cadence policy is written
  into the doctrine doc — **MET** (landmark cadence; CLAUDE.md
  merge-protocol step 2 now names the judge for headline-statement arcs).
- The wrapper fails closed on: missing/wrong-version binaries,
  designated-list mismatch between `judge-config.json` and `Audit.lean`,
  or any judge error — **MET** (plus a pristine-tree check on
  deps/comparator, per the standing trust-tools rule).
- Added at close-out: `scripts/comparator-setup` reproduces the judge
  environment from a clean `deps/` at the recorded pins (clone, build,
  landrun install, upstream smoke pair). Needs network, so it runs
  user-side; its steps are exactly what this session performed and
  verified piecewise.

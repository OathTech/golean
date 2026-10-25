# What a release is (RULED 2026-10-12)

**Status: RULED** — [USER] Mike 2026-10-12 (D2: agreed as written) on the [AGENT] proposal of the release-readiness backlog
(`docs/2026-10-12_release-readiness.md` §0, §5). Nothing here is ruled until the [USER] says so; until then no
`release/*` tag exists and `lakefile.toml`'s `version` stays where it is (a release is the [USER]'s act). Drafted by
the records lane `docs/release-records-1012`, 2026-10-12, from the review's §0 proposal: the 2026-10-03 re-pin offer to
the logic team (`docs/changelog/61958f2e-WINDOW.md`, tag `logic-offer/2026-10-03`), generalised and made public.

## 1. A release is

1. **A tag** `release/<YYYY-MM-DD>` on a commit of `main` (annotated; the date is the tagging day, UTC; a second
   release on one day takes `release/<date>.2`). The tagged commit is the release; nothing outside the repository at
   that commit is part of it.
2. **The pinned toolchains at the tag**, unchanged by the release itself: Lean `lean-toolchain` =
   `leanprover/lean4:v4.35.0`; the Go oracle `baselines/go-oracle-pin` = `go1.26.5` (never floated — CLAUDE.md, the
   trusted surface #2). A pin move is a separate, earlier commit with its own full run and written reason.
3. **The merge gate green at the tag**: `capped scripts/ci --diff`, RESULT: PASS, on a clean tree at the tagged commit,
   judged against the tracked baselines at that commit (`baselines/native-full.tsv`, `baselines/negative-full.tsv`,
   `baselines/untriaged-count`, `baselines/untriaged-ids`, `baselines/stdlib-pin.tsv`, `baselines/pins/`). The run's
   wall time, row counts (PASS / FAIL, differential and negative) and exit code are written into the release record
   (§3); its logs are not committed.
4. **A changelog frozen from the previous release tag**: one file `docs/changelog/<prev-tag-commit>-RELEASE.md` (the
   first release starts from the offer commit `20d3946d` and FREEZES `docs/changelog/20d3946d-WINDOW.md` at the tag),
   rows in the existing convention — one row per landing train, newest first, each naming what a consumer of GoCore
   programs, the wire, the CLI or the raft subject can observe, the trusted surface touched, and its [USER] authority
   (relayed) — and a cumulative summary at the top measured against `git show <prev-tag>:<path>`, as the
   offer's summary was.
5. **A stated-limits section**, in that changelog, one place, each a limit and not a gap read as closed. The template is
   the offer's ten STATED LIMITS (`docs/changelog/61958f2e-WINDOW.md`, «STATED LIMITS of the offer»: the memory floor;
   the relation retired and parked (2026-10-20, tag `relational/last-main-2026-10-20`: the pool/registry half, C4's run-level
   preservation, `NoRefusal`'s sequential-only domain and the false run-level converse are no longer claims — `Prefix`/`Finish`
   and the `stepFn_eqns` library remain); the legacy evaluation-order triple; raw location ids in the readout; setup as a
   premise and init-time printing refused; the corpus limits; the deferred items; the
   native lowering without a correctness theorem and the Platform instance gc linux/amd64). Each release re-derives the
   list against the tag; the backlog's debt table (`docs/2026-10-12_release-readiness.md` §3) is the current input.
6. **The three release predicates, reported separately** — each its own line in the release record, never folded into
   one green (`docs/2026-09-05_master-plan.md` §7.3, «Three release predicates, PROPOSED [AGENT]», quoted):
   1. «**No unclassified failures** — every non-PASS row on a named row (today's E3 arithmetic; a records predicate).»
   2. «**Zero known wrong answers within an explicitly named supported profile** — counting OPEN wrong-answer entries
      […] and GUARDED wrong-answer classes (refusals that replaced a wrong answer, e.g. the BUG-098 guard) alongside the
      untriaged counter; the profile is named by the [USER] (PENDING […])» — still PENDING as backlog decision D1.
   3. «**A justified behavioural envelope for that profile** — the latitude inventory's pinned/narrowed/unknown/refused
      axes enumerated for the profile, each with its re-envelope obligation or recorded gc deviation (§3.D), stated as
      an envelope, not as "all latitude included".»

   §7.3's rule carries over: «Intentional reds stay red; expected Go behaviour is never edited to make a release
   green». A predicate that does not hold is reported as not holding, with its count; it does not block the tag unless
   the [USER] rules that it does.

## 2. Who tags

The [USER] decides that a release happens and signs off the tag at that moment. An agent may prepare everything below
on a branch (the frozen changelog, the release record, the gate run) and pose the tag as a question; it never creates a
`release/*` tag, bumps `version` or pushes without that sign-off (CLAUDE.md, merge protocol step 6 and the global
push rule). Pushing the tag is a separate sign-off.

## 3. The procedure

1. On a branch off `main` (a records lane): freeze the changelog (§1.4) and write the stated limits (§1.5) and the three
   predicates (§1.6) with their counts and sources (`scripts/check-bugs.sh`'s summary line, the open `docs/BUGS.md`
   entries, `artifacts/coverage/latest.tsv`, the latitude inventory).
2. Run the audit ask on the branch (CLAUDE.md, merge protocol step 3); merge on sign-off.
3. At the merged tip, on a clean tree: `capped scripts/ci --diff` (§1.3), then the claim-point kernel check in the
   form that exists today (every figure below measured 2026-10-22 on this box under the nono agent sandbox with
   `--inadvisably-no-sandbox`, i.e. NOT under Lake's `bwrap` sandbox; `docs/operational-lessons.md`, «Lean 4.35»):
   - (a) The plain `lake check` is the claim-point gate — the literal command, on an Oath box outside the agent
     sandbox: `CAPPED_MEM_MAX=64G capped lake check`. Expected: «Lean default kernel accepts the solution», «Uses
     axioms: propext, Quot.sound, Classical.choice», exit 0, about 3.5 min, largest process 2.7 GB. Exit 2 with a
     `bwrap` line means Lake's sandbox cannot start there — unverified on this box from inside the agent sandbox
     (`/usr/bin/bwrap` is not setuid, `kernel.apparmor_restrict_unprivileged_userns=1`, the AppArmor profiles are
     unreadable from here) — and then the only form is `lake check --inadvisably-no-sandbox`, which the toolchain
     labels «not trustworthy»: there is no sandboxed gate on that box, and the release record (step 4) must say so.
     PLUS, on the same export, the four bundled external kernels that work, run by hand exactly as Lake invokes them
     (`Lake/CLI/Check.lean`, `bundledKernels` and `runExternalKernel`: `LEAN_ABORT_ON_PANIC=1`, the export path as
     the last argument; `T` is the toolchain's `bin`, `~/.elan/toolchains/leanprover--lean4---v4.35.0/bin`); the box
     default cap suffices for these (the largest is con-leche at 6.6 GB):

     ```
     LAKE_CHECK_EXPORT=1 capped lake check > export.ndjson          # Lake's build-and-export half alone: 35 s, 2.7 GB; a 0.95 GB, 16.5 M-line export
     LEAN_ABORT_ON_PANIC=1 capped $T/leanchecker-paranoid --silent --from-export export.ndjson   # silent; exit 0 = accepts (225 s, 1.7 GB)
     LEAN_ABORT_ON_PANIC=1 capped $T/lean4lean --import export.ndjson       # «checked 178476 declarations», exit 0 (236 s, 1.4 GB)
     LEAN_ABORT_ON_PANIC=1 capped $T/con-leche export.ndjson                # «con-leche: accepted 178479 declarations (--verified)», exit 0 (27 s, 6.6 GB)
     LEAN_ABORT_ON_PANIC=1 capped $T/con-ron export.ndjson                  # «con-ron: accepted 178479 declarations (--verified)», exit 0 (18 s, 3.4 GB)
     ```

     About 9 min in all (the declaration counts move with the tree; what matters is exit 0 and the acceptance line of
     each). Lake itself offers no kernel subset: `lake check --paranoid` runs all five bundled kernels or none
     (`Check.lean:623`; `enable_nanoda` / `external_kernels` are `lake comparator`'s configuration, not `check`'s).
   - (b) `lake check --paranoid` (`CAPPED_MEM_MAX=64G capped lake check --paranoid`; 975 s, largest process 42 GB)
     becomes the release command once nanoda is fixed upstream. Today it is red, deterministically and independent
     of the sandbox: `nanoda_bin` 0.4.19 crashes on this export with Lake's own configuration (`num_threads` 4, the
     trio permitted, `nat_extension` and `string_extension` on) — «thread 'thread_3' has overflowed its stack» /
     «fatal runtime error: stack overflow, aborting», SIGABRT, exit 134 — after about 249 s at 43.5 GB, twice on the
     export alone; `RUST_MIN_STACK=4G` is ignored (nanoda sizes its worker stacks itself; its help has no stack
     option); the other four kernels and Lean's own accept the same export. That is the report to file upstream.
   - (c) `lake comparator` — the surface kept on main for the raft-proofs customer (366 theorems: every theorem of
     `Equations.lean` (300; 234 of them `@[stepFn_eqns]` simp-set members), the G11 family, the `Prefix`/`Finish`
     laws, the output-fold bridge, `enterFrame_declared`, the `Choices.consumeAt*` laws, the thirteen G16
     table-monotonicity statements) judged against its FROZEN
     challenge `Contract/Challenge.lean` per `comparator.json`
     at the root (release-readiness row 43, [USER] 2026-10-23): `CAPPED_MEM_MAX=64G capped lake comparator` (the box
     default cap suffices). Expected: «Lean default kernel accepts the solution», «Your solution is okay!», exit 0,
     about 20 s (measured 2026-10-23 inside the agent sandbox with `--inadvisably-no-sandbox`: 19.0 s, largest process
     1.84 GB; the `bwrap` caveat of (a) applies unchanged). Exit 1 names the first statement, definition or axiom that
     mismatches — a kept theorem whose statement was edited without the challenge being updated deliberately (with a
     changelog row), a stale generated half (`scripts/gen-contract --check` names it first in the speedbump form,
     `scripts/check-comparator`), or a proof that reached a non-standard axiom. What this run does NOT see: the
     frozen text is re-elaborated against the live definitions, so a drift that enters through a definition's
     signature (an inserted implicit or default argument, an `abbrev`) moves the kept statement and the challenge
     alike; that is caught only across a pin, by the consumer's `--challenge-from-export` route
     (`scripts/contract-export`). The judge is Lake's syntactic comparison of the two exports; the kernel replays
     the solution. Nothing is re-pinned to make it green.

   A red run of the gate, of any kernel in (a) or of the comparator in (c) stops the procedure; nothing is re-pinned
   to make it green.
4. Write the release record — a short section at the top of the frozen changelog: tag name, commit, toolchain pins,
   the gate run's result line, the three predicates — and commit it on a records branch merged on sign-off. (The record
   cannot name its own commit; the tag goes on the record's commit, and the record names the gated commit it
   documents, which must be its parent or have only records commits between them.)
5. On [USER] sign-off: `git tag -a release/<date> <commit>`; optionally bump `lakefile.toml` `version` in the record
   commit if the [USER] asks for it. Push only on a separate sign-off.

## 4. Stated limits the first release carries (the rulings so far)

- **Pre-`main` aborts are outside the differential's observation scope** (BUG-107, five rows refusing
  by name): a package initializer that panics or deadlocks before `main` cannot be authenticated as a
  gc abort because the harness registers its crash channel from `main`. [USER] Mike 2026-10-12
  (D3): (accepted and stated as a limit).
- **Static-initialization-dependent programs** (BUG-061: gc folds some package-level initializations
  into the data section; the model schedules them): [USER] 2026-10-12 (D1): (refuse the case if excluding it is easy) — the refusal by name is a lane; if no cheap exclusion exists, the release names the
  profile that excludes the shape and keeps the row as a known red.
- **The abort window** (punch-list item 29, from the sched-boundary review 2026-10-12): a goroutine's
  output beside main's abort is not a scheduling boundary (`atBoundary_of_abort`; «B3, deferred»), so the
  machine never interleaves a child's `print` between main's last output and its panic — pinned gc does,
  dominantly (994 of 1000 runs at GOMAXPROCS=2 on the probe). A known admitted class, NAMED as a stated limit and not widened: [USER] Mike 2026-10-12
  (items 1 and 3-6 approved) (item 3 of the ask = this limit; the [AGENT] coordinator read the approval as approving the
  limit as written here, the ask having offered «name it, or widen»). Widening (a boundary at the abort) would
  touch `atBoundary_of_abort` and the driver's terminal-priority classification — a pinned-statement question
  left for a later ruling.
- **Go version** (the diversity runs of 2026-10-13, punch-list rows 32 and 35): the language is Go 1.26's — gc 1.27's
  generic methods are refused at parse; fidelity is to gc go1.26.5 exactly — a user on gc 1.25.0–1.25.3 sees no
  panic on `any(f) == any(f)` where the model and the spec panic (golang/go#76010); abort TEXTS are
  version-sensitive (the `panic(nil)` prefix in 1.27, `[recovered, repanicked]` since 1.26, the unhashable-key
  phrasing, `print` of floats) — observation-format sensitivities, not semantics. `scripts/go-version-diversity`
  measures a toolchain against the pinned record; it never re-pins.
- **The enumerator's practical reach** (fresh-eyes pass F3): the DFS enumerator's defaults (`--max-sites 8`,
  `--work-cap`) are tripped by most two-goroutine shapes; the refusal is loud, the dedup engine is the
  alternative, and the strict lane's depth guard is what the gate relies on.
- **The strict lane's comparable surface** (F4): outside seeded mode the Go observer has no pointer, slice, map or
  channel arm, so a strict row whose result holds one of those cannot be compared and is a visible red.
- **gc's size limits are mirrored by over-approximation** (train 9, punch-list row 34; `tools/nativefrontend/gclimits.go`):
  a channel element type of 64 KiB or more, an array larger than the address space, a struct or a function-argument
  list of 2^50 bytes or more is refused after type-check with gc's text — at EVERY mention of the type, including
  declarations and dead code gc would never size, so some programs gc builds are refused by name (the message says
  so; 25 such shapes pinned as refused-by-design in `tools/nativefrontend/gclimits_test.go`). [USER] Mike 2026-10-13, relayed: (refuse the case rather than open the door to special-casing; support may come later). A body-less user function is refused the same way (BUG-126).
- **A `package main` with no `func main` is refused** by the frontend's default mode, as gc refuses to build it
  (BUG-125, `tools/nativefrontend/entrymode.go`, the same ruling). The differential corpus exports its subjects with
  `--subject`, which skips only that rule; a consumer exporting a main-less package passes it too, or adds a `main`.
  No whole-program mode for such packages — later support left open.
- **A variable-length `make` past the budget is a memory kill, not a refusal** (punch-list row 30's open half, row
  31(d)): a constant-length `make` whose count × element footprint exceeds the budget refuses by name at decode, but
  when the length is computed at run time the backing is built, and a count × footprint past the cap ends the run
  under `capped` with exit 137 — loud, never a wrong answer, but an apparatus kill rather than a named refusal. The
  core guard at the `make` site (the `sliceCapBudget` template) is a lane awaiting the [USER]'s word.
- **Compiler directives are refused by name** (the Codex zero-context pass F2, punch-list row 38; BUG-127;
  `tools/nativefrontend/directives.go`): in every user unit, any `//go:` directive outside the allowlist —
  `//go:build`, `//go:noinline`, `//go:generate`, the three with no effect on the compiled program — and any
  `//line`/`/*line` directive refuses the export at file selection (`//go:embed`, `//go:linkname`, the codegen and
  race pragmas, unknown verbs gc ignores: all refused; no directive is modeled); the three allowed verbs only in the
  placements gc accepts (a directive after code on its line, a `//go:build` after the package clause, a
  `//go:noinline` no func or method declaration follows: refused as gc's «misplaced compiler directive»). [USER]
  Mike 2026-10-13, relayed: (item 3 agreed), under (refuse the case now; support may come later).
  Rows `directives/*` (three red by design, five controls, nine negative).
- **The model's runtime defaults** (F3, row 39; BUG-128): the semantics is Go 1.26's with the MODULE-mode runtime
  defaults — `panic(nil)` is `*runtime.PanicNilError`. No GODEBUG setting is modeled: `//go:debug` lines (any user
  unit) and go.mod `godebug` lines/blocks refuse by name. The differential oracle is pinned with
  `GODEBUG=panicnil=0` on every `go run`, because gc in GOPATH mode (no go.mod — the corpus's mode) defaults to the
  LEGACY `panic(nil)` (measured at go1.26.5: `recover() == nil` is `true` there, `false` under the pin and in a
  `go 1.26` module). A consumer comparing a wire's run against gc by hand must run gc the same way (the pin, or a
  `go 1.21`+ module with no godebug override). Stated limits of the same contract: in GOPATH mode every GODEBUG
  setting is at its go 1.16-era default and only `panicnil` is pinned — sound at the pin because no other
  version-dependent setting is reached by an admitted stdlib member (measured against `internal/godebugs/table.go`;
  an obligation on every future admission, `docs/stdlib-admission-register.md`); a `go.work` `godebug` line is an
  override the frontend never reads (measured: it flips a module's answer while the export succeeds) — do not build
  inside a workspace that sets one; `//go:debug panicnil=0`, the one source-level match for the pin, is refused
  like every `//go:debug`. The contract is stated in `docs/cli.md` §1.
- **A blank struct field's operand is not evaluated** (row 37; BUG-129/BUG-130): the field takes the zero
  value — spec#Comparison_operators compares «non-blank field values» only — and the operand may be a constant,
  `nil` or a plain variable read (an identifier naming a variable, a package-qualified variable, a struct VALUE's
  field selection with no pointer on the path); any other operand refuses the literal by name, at package level
  the initializer with it. The reason is gc's realization, which is not an evaluation: it drops a side-effect-free
  blank operand together with its run-time panic (`walk/complit.go:231` via `staticinit.isSideEffect` — a negative
  shift count, an interface comparison over an uncomparable dynamic type, under any pure wrapper: gc answers, an
  evaluating model panics) and never evaluates a package-level struct literal's blank operand at all, calls
  included (`staticinit.initplan`). [USER] Mike 2026-10-14 (both halves agreed); the mirror of gc's census is deferred,
  later support left open (ledger §5.1 item 9). Rows `structs/blank-field-*` (13 PASS, 14 red by design, one negative).
- The ten limits of the 2026-10-03 offer (`docs/2026-10-03_offer-to-logic-team.md`) stand.


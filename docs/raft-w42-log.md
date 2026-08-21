# Raft W4.2 campaign log — the machine-twin harness

Lane: `raft-w42` (worktree `.claude/worktrees/raft-w42`), branch `raft-w42`
off `main` @ `4ef05649` (the W4.1 tip). Charter: harness design
(`docs/2026-08-20_machine-twin-harness-design.md`) §8's W4.2/W4.3 slices —
the logger swap + re-owed census, the n-node twin, the §7 trace ok-tier —
scoped CORPUS-FREE: this lane owns `raftsubject/`, `raftharness/`,
`tools/raftsubject/` and this log; the POR slice concurrently owns
GoCore/`Corpus/`/`baselines/`. Any corpus guardrail this lane wants is an
OWED ROW (§ owed-rows below), never landed here.

Read-first companions: the harness design (§2 the event vocabulary + the
recorded Ready-harvest narrowing, §4 S1–S4, §5 the ruled logger seam, §7
the trace plan), `docs/raft-w41-log.md` ("What the ruled logger swap
re-owes" — item 1's charter), `docs/raft-w3-log.md` (instruments),
`docs/2026-08-15_raft-push-p0-scoping.md` §6 (the executable Agreement
predicate this twin integrates).

## Environment notes (2026-08-21)

- Fresh worktree; `scripts/setup-deps --from /home/dev/projects/golean`
  exit 0 (goose 3be88bb, perennial 43d4efa, raft 56e3200, iris-lean
  3877dbe, go c19862e5f8); `proofs/.lake/packages` populated from the
  primary checkout (batteries/iris/Qq at the manifest pins).
- No runtime code (GoCore, `tools/nativefrontend/`, `Corpus/`,
  `baselines/`, `scripts/`) is touched anywhere in this arc, so per-landing
  gates run `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` with the
  two visible NOT-RUN notes, per the CLAUDE.md hatch contract. Heavy gates
  staggered against the concurrent POR lane (free -g checked first).

---

## Item 1 — the logger swap (the Q2 ruling executed) + the re-owed census

**Landed.** Upstream `logger.go` is vendored VERBATIM (mode `verbatim` in
`derive.py`'s VENDOR table); the D-5 no-op overlay
(`tools/raftsubject/overlay/raft/logger.go`) is DELETED. The one delta the
frontend still forces is recorded as **D-12** (ledger below): the two
package-level initializers lose their `log.New(...)` calls and the orphaned
`io` import drops — a package-level `var` has no per-declaration quarantine
(G-3 / handoff H-11), so an unlowerable initializer refuses the WHOLE
export. Land H-11 and D-12 retires to zero.

**The 144→2-3-line claim, RE-MEASURED** (artifacts/w42, diff vs
`deps/raft/logger.go`):

| | diff lines vs upstream |
|---|---|
| D-5 no-op overlay (retired) | **142** (the whole 142-line file replaced by a 116-line no-op) |
| the swapped tree | **11**, of which **3 are code** (2 initializer lines rewritten to `&DefaultLogger{}`, 1 dropped `"io"` import) and 6 are the D-12 recorded-delta comment + 2 context |

So the design §5's "three lines, not two" is confirmed exactly; its
"eleven fail-closed stubs" is now TEN — the §5 measurement predates W4.1's
fmt desugar, and `header` (`fmt.Sprintf("%s: %s", lvl, msg)` — constant
format, `%s` over strings) is inside the modeled subset and LOWERS.

**Observable weight of D-12, stated:** under `go run`, a Logger call
BEFORE the harness installs its logger nil-derefs inside `DefaultLogger`
(the embedded `*log.Logger` is nil) instead of printing to stderr — loud,
never silent; under the machine the same call is a fail-closed quarantined
stub. Both witnessed by the teeth probe below. `assertConfStatesEquivalent`
keeps its teeth through whatever Logger the harness installs — the whole
point of the ruling.

### The re-owed census, run (what W4.1's "0 LIVE" becomes after the swap)

`sweep.py` at the swapped tree (artifacts/w42/sweep-post-swap.txt;
`frontier.py` EXPORTS CLEAN, `derive.py --check` clean, subject
`go build` clean):

- **PASS 1: 24 quarantined subject declarations** (pre-swap tree
  re-derived and re-swept at THIS tip for an exact diff: **14** — the
  swap's delta is EXACTLY the ten `DefaultLogger` formatting methods
  joining, nothing leaving; artifacts/w42/sweep-pre). Imported stubs
  30 → **46** (the `log` package's declaration-only stubs join).
- **5 STATICALLY LIVE** quarantined subject declarations —
  `DefaultLogger.{Infof, Debugf, Warningf, Error, Errorf}` — plus
  **2 LIVE imported stubs** — `log.Logger.{Panic, Panicf}`, which is
  `DefaultLogger.Panic/Panicf` lowering and stopping one hop later.
  That is the W4.1 re-owed table's seven distinct methods, measured
  on the wire rather than predicted from grep.
- **RESIDUAL SINKS: 7** — the same seven. This census is NOT closed the
  way W4.1's was, and honestly so: the sweep never neutralises LIVE
  declarations, so what `DefaultLogger`'s bodies would call
  (`header`, `fmt.Sprint*`, `Output`, `os.Exit`) sits unmeasured behind
  them. It does not need measuring: the whole family is dead under the
  same dynamic argument, below.

**A count reconciliation, recorded:** W4.1's clause-1 headline said "15
quarantined in PASS 1"; the reproduction at this tip (same tree content,
this frontend) censuses 14. The 15 was recorded mid-arc before the
audit-fix round's `%x`/`%q` Stringer-precedence widening landed in the
same branch; one rendering declaration evidently lowered with it and the
prose number was not re-derived at the audit tip. Reconstructed, not
verified per-declaration; the tracked artifact pair (sweep-pre /
sweep-post-swap) is the number of record going forward.

### The dead-DYNAMICALLY argument (owed item ii), and why it is checkable

The seven statically-live entries are all dead under the twin, but dead
DYNAMICALLY — a static census over-approximates interface dispatch (a call
to `Logger.m` edges to every concrete `m`). The argument, in three parts,
each mechanically witnessed:

1. **The harness installs through BOTH seams before any node (or storage
   use) exists.** Constructor order, visible in the harness source:
   `lg := &harnessLogger{}; raft.SetLogger(lg)` is the first act (covers
   the six `getLogger()` sites — the registry is written once, pre-run,
   and never again); `cfg.Logger = lg` on every node's Config (covers
   every `r.logger.*` call, via `Config.validate`'s nil-check taking the
   assigned value). Package init cannot log first: `raftLogger`'s
   initializer merely aliases `defaultLogger`, and no `init()` in the
   subject tree calls a Logger method.
2. **The stubs have TEETH, witnessed** — so a green run is a meaningful
   negative. `logger-teeth-probe-main.go` (runprobe `--expect-stop`, new
   mode): the SAME drive with NO logger installed stops the machine at
   `frontend-quarantined: method raft.DefaultLogger.Infof (...)` —
   verbatim first stop — the moment `newRaft` logs, and dies loudly under
   `go run` (the D-12 nil-deref). PASS.
3. **The green half, machine-checked.** `logger-installed-probe-main.go`:
   the W4.1 THE-MOMENT drive with the harness logger installed through
   both seams runs GREEN under both oracles and agrees at **1111035** =
   the registry-seam teeth digit (a deliberate out-of-bound
   `MemoryStorage.Entries` routes `getLogger().Panicf` into the installed
   logger's fixed-string panic, recovered and folded into the summary —
   a call `Config.Logger` alone could NOT catch, exercising the §5
   amendment positively) + the unchanged 111035 drive summary. Every
   quarantined `DefaultLogger` body is a machine-STOP if called; the run
   is green; therefore none was called. The twin (item 2) re-witnesses
   this on every green n=3 run.

**The harness logger itself** (harness-owned, no verbatim-ness claim):
eight empty bodies + four fixed-string panics (`Fatal` panics too — no
`os.Exit` to model; "stop the machine" is the honest reading). It is
STATELESS — no fields, so its footprint is empty and sharing ONE value
across all n nodes cannot appear in any pairwise-disjointness obligation
of the §6 shared-nothing reduction; a buffering logger would be shared
mutable state on every node's every event and is explicitly ruled out
(per-node + a §6 re-run if ever needed).

### Subject-delta ledger additions (requirement (c) of the §8.6 ruling)

Continuing D-1…D-11 (W2 §4, W3 §1, W4.1). **D-5 is RETIRED by this item**
— a dated correction is appended at its W2-log entry; its noopLogger,
including the "Panic/Panicf no longer panic" weakening H-2 recorded, is
gone from the tree.

**D-12 `raft/logger.go`, the two package-level Logger initializers**
(item 1). Exact-text-keyed `SUBJECT_PATCHES` derivation patch:
`defaultLogger`/`discardLogger` lose their `log.New(os.Stderr,...)` /
`log.New(io.Discard,...)` calls (unlowerable package-level initializers,
G-3/H-11) and become bare `&DefaultLogger{}`; the orphaned `io` import
drops. Everything else in the file — the Logger interface,
`SetLogger`/`getLogger`/`ResetDefaultLogger`, `DefaultLogger` and all its
methods, `header`, the `raftLoggerMu` mutex — is upstream text.
**Observable weight:** a Logger call before the harness installs its own
nil-derefs loudly under `go run` (upstream would print to stderr) and
stops the machine at a quarantined stub; unreachable under the twin
(the dead-DYNAMICALLY argument above, both halves probed). Retires to
ZERO when H-11 lands. The patch keys on upstream's exact `var (...)`
block and refuses on drift.

**Gate:** `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
item-1 commit — see the exit-state section for the verbatim result lines.

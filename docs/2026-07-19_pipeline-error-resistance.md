# Pipeline error-resistance — hardening every stage (2026-07-19)

**Goal (the user's framing).** GoLean is an infrastructure we ride up to a
complete Go verification tool. Its fundamental structure is already resilient —
**a proof pipeline resting on differential testing**. The task is to make *each
stage* genuinely error-resistant against **both** error kinds, so that an
error-prone (non-malicious) agent is *guided to get it right*: the wrong move
fails loudly and locally, the right move is the path of least resistance.

- **Commission** — claiming something false (a vacuous law, an overclaiming
  docstring, a case that passes by luck, a frontend lowering that emits wrong IR).
- **Omission** — failing to catch something wrong or missing (an untested
  feature, an unbacked claim, a hidden stuck case, a dropped known-bug).

**Design principle:** prefer **build-enforced / re-runnable gates** over
honor-system discipline. A gate that fails the build is worth ten conventions.
Every past defect (`wp_assign` hred vacuity; `wp_deref_store` re-shipping it; the
F1 struct-write hidden stuck) slipped a *manual* check; each becomes a standing
automated gate here. Mechanisms adapted from ACL2Lean (a more mature sibling; see
the strategy survey folded in below).

## The trust chain, stage by stage

```
real Go ──[S0 frontend: NativeToIR]──▶ GoCore IR ──[S1 interpreter: Eval]──▶ value
   │                                                        │
   └────────────── differential oracle: `go run` ──────────┘   (S1 gate)
GoCore IR ──[S2 correspondence]──▶ Rel.Step ──[S3 relation]──▶
        ──[S4 WP laws]──▶ ──[S5 adequacy]──▶ safety
```

### S0 — Frontend (Go → GoCore IR)
- **Commission:** wrong lowering (F1: address path emits a value-read base).
- **Omission:** a feature silently unsupported, or wrongly-lowered so it fails
  *downstream* (stuck at interpret) instead of at the boundary — hidden.
- **Gates:**
  - [ ] **Fail-closed audit (re-runnable):** assert the frontend emits an explicit
    `unsupported`/error at the boundary for every unhandled construct — never a
    silent wrong node. Tamper-style: feed constructs known-unhandled, assert a
    boundary failure, not a downstream stuck. (ACL2Lean §3 tamper tests.)
  - [ ] **Supported-features manifest ↔ cases cross-check** (ACL2Lean
    `check-no-shadow`): the list of features the frontend claims to lower is
    scraped and diffed against the set exercised by differential cases; a claim
    with no exercising case fails. Directly prevents the F1 class ("docs say
    field/index works" while the write path is untested).

### S1 — Differential testing (interpreter vs real Go) — *the foundation*
- **Commission:** a case "passes" while the interpreter is wrong (weak case, or
  the oracle coincidentally agrees).
- **Omission:** a feature has no case; or a `FAIL` silently flips to a wrong
  `PASS`; or a known semantic gap is forgotten.
- **Gates:**
  - [x] **Pinned baseline + diff** (`baselines/native-full.tsv`,
    `scripts/coverage-baseline-diff`): result/id/stage per case, sorted; a
    PASS↔FAIL flip or stage change fails. *Strengthen:* run it **in the gate**,
    not ad hoc, and carry the whole report (ACL2Lean §1 golden full-report diff,
    with a `.actual` for re-baselining).
  - [ ] **Expectation-class ratchet** (ACL2Lean §6): tag each case `match` /
    `unsupported` / `known-bug`. `unsupported` **fails if the tool now produces a
    value** ("unexpectedly better" fails until reclassified) — this is what stops
    silent drift *in either direction* and would have surfaced F1's write path
    the moment it started/stopped working.
  - [ ] **Three-layer sufficiency** for each feature (isolated case + edge
    enumeration + integration/fuzz), per `docs/native-frontend-goal.md`, so
    `green ⇒ target covered`, not `green ⇒ happy path only`.
  - [ ] **`docs/BUGS.md` ↔ tagged-cases bidirectional cross-check** (ACL2Lean §5
    `check-bugs.sh`): every known semantic gap (F1, the 80 `lean-observation`
    fails triaged) is a canonical entry; a `bug:BUG-N` tag must name an open bug,
    and every open differential-pinned bug must have a live tag. Known limitations
    can't rot in prose or be silently dropped.

### S2 — Correspondence (interpreter ⇄ relation)
- **Commission:** the correspondence *statement* is false. **Omission:**
  constructs uncovered; the whole thing is **currently unproven**
  (`interpreterSound/PanicStatement` are `def : Prop`, not theorems — the two
  halves are formally disconnected islands).
- **Gates:**
  - [x] **Three-state honesty** (started, `proofs/Audit.lean` ledger): the
    unproven Props are marked *stated, not proven* — nothing counts them as
    established.
  - [ ] **Totalize Eval's big-step cluster** (F3) → convert the Props into
    theorems; **this joins the islands** and is the single highest-leverage unlock.
  - [ ] **Proven-instance coverage golden:** the hand-proved correspondence
    instances (currently 5) recorded in a golden table so their count/set can't
    silently shrink.

### S3 — Relation (`Rel.Step`)
- **Commission:** a rule mismodels Go. **Omission:** a missing rule (fail-closed
  stuck — fine, but incompleteness); a *skeleton gap* (results-allocation) that
  looks complete.
- **Gates:**
  - [ ] Every relation rule is pinned by ≥1 proven correspondence instance OR a
    differential case whose interpreter path it mirrors (once S2 lands).
  - [x] Skeleton gaps documented in the module header (results-allocation,
    fall-through) — *strengthen:* each becomes a tracked BUGS.md entry so it can't
    be forgotten when someone builds atop it.

### S4 — WP laws
- **Commission:** vacuous / overclaiming law. **Omission:** missing law.
- **Gates:**
  - [x] **In-build axiom-allowlist gate** (`proofs/Audit.lean`,
    `#guard_msgs in #print axioms`): a `sorryAx`/`native_decide`/new axiom in any
    listed theorem fails the build. Type-checking is *not* enough — the kernel
    accepts `sorryAx`. (ACL2Lean §2.)
  - [x] **Non-vacuity witness gate** (`proofs/Audit.lean`): every user-facing law
    is referenced via its discharge witness (`wp_assign_lit`,
    `wp_deref_store_ref`); deleting a witness/law fails the build.
  - [x] **CLAUDE.md non-vacuity rule + "report mechanically"** convention: no
    "usable"/"complete" in a docstring without a witness; a `∀σ`-over-state
    premise is the smell to check first.
  - [ ] **Close the witnesses' last open premise:** `wp_assign_lit` /
    `wp_deref_store_ref` still leave `hstore` (`∀σ` store-typing) unproven — mark
    `◌`, and discharge it for a concrete cell so a witness carries zero
    hypotheses (`◌ → ✓`).

### S5 — Adequacy → safety
- **Commission:** adequacy overclaims (panic-exclusion; NotStuck scope).
  **Omission:** never instantiated end-to-end.
- **Gates:**
  - [x] Axiom gate on `go_adequacy`; honest scoping in its docstring.
  - [ ] **End-to-end adequacy witness (`◌ → ✓`, the capstone):** a concrete GoCore
    program, `WP` built from the shipped laws (`wp_seqn` + `wp_assign_lit`), fed to
    `go_adequacy`, yielding a **closed** `adequate …` with no remaining
    hypotheses. This is the one artifact that proves the whole WP→adequacy chain
    composes on ≥1 example — without it, "the chain composes" is unproven at the top.

## Cross-cutting infrastructure

- [x] **`proofs/Audit.lean`** — in-build axiom + non-vacuity gate (a default
  target; a weakened claim fails `lake build`). Three-state `✓ / ◌ / ✗` ledger.
- [ ] **One `scripts/ci` gate** bundling every check (ACL2Lean `just ci`):
  core build, proofs build (⇒ Audit), `gocore-eval-tests`, escape-hatch grep,
  baseline diff, BUGS cross-check, manifest cross-check. One command an agent
  runs before claiming done; CI runs the same.
- [ ] **Escape-hatch source gate** (`scripts/proof-audit`): grep the tree for
  `sorry`/`admit`/`native_decide`/`axiom`/new `partial` in proof-facing files;
  fail if any appears where it's disallowed. (Complements the in-build axiom
  gate — catches them at edit time, cheap, no Lean.)
- [ ] **"Report mechanically, not with adjectives"** everywhere (ACL2Lean §7):
  claims cite their evidence; corrected claims carry audit provenance
  (`FlattenSpike.lean`-style `(corrected 2026-…, audit N)`), as `wp_deref_store`
  now does.
- [x] **Async-result failure diagnosis** rule (CLAUDE.md housekeeping) — a
  background task's partial signal ≠ total failure; inspect the artifact.

## Priority order (recommended)

Highest leverage / lowest risk first; each is a standing gate, not a one-off.

1. **Bundle `scripts/ci`** + wire the baseline diff and escape-hatch grep into it
   (makes "the gate" one reproducible command — the thing an agent runs). *Cheap.*
2. **`docs/BUGS.md` + `check-bugs.sh`** cross-check; enter F1 and the triaged
   `lean-observation` gaps. *Cheap; de-hides omissions.*
3. **Expectation-class ratchet** on differential cases (S1) + **feature↔case
   manifest cross-check** (S0). *Medium; kills the F1 class.*
4. **End-to-end adequacy witness** (S5) + **close `hstore`** (S4). *Medium; turns
   the two biggest `◌`s green — proves the proof chain composes.*
5. **Totalize Eval big-step** (S2/F3) — joins the interpreter and proof islands.
   *Heavier; the honest "end-to-end" unlock.*

Done this session: `proofs/Audit.lean` gate, CLAUDE.md non-vacuity + async-failure
rules, pinned baseline + diff, `wp_deref_store` correction + witness.

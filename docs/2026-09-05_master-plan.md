# The GoLean master plan — the whole roadmap to a "good" Go semantics, as understood on 2026-09-05

Status: PLAN OF RECORD (index), docs only. [AGENT]-authored (lane
`master-plan-0905`, worktree off `main` @ `9343a310`, rebased onto
`7677865a` when the `e13-b` train landed mid-gate — §0.2 addendum);
[USER]-commissioned.
Every number below names the command or file:line it came from; every
status is one of the six words in §0.3; every decision cited carries
[USER]/[AGENT] provenance. This repo makes NO verification claims
(`CLAUDE.md`, "What this repo is"; `docs/2026-08-31_repo-split-plan.md`),
and nothing here is one.

---

## 0. Purpose, date, how to read

### 0.1 The commission

[USER] Mike, 2026-09-05, verbatim as relayed by the [AGENT] coordinator
(cited as relayed, not firsthand — the U0-incident convention): «I think
it'd be good to write this all up in a dated 'master plan' doc, and then
I can get another agent to do a whole-project review. … The plan should
include the whole roadmap to making golean a 'good' go semantics (as we
understand it now) broken down by technical packages and then broader
goals if there are some we haven't decomposed yet».

Two readers: (a) the [USER]; (b) an independent whole-project review
agent that will use this document as its map. Everything is therefore
written to be CHECKED, not believed: §6.3 is the review brief.

### 0.2 The snapshot this document describes

- `main` @ `7677865a`, 2026-09-05 (`git log -1 main`) — the `e13-b`
  round-17 records commit; its message records the gate tail: PASS;
  cases=3593 pass=3347 fail=246; baseline diff FULL 3593/3593; twin
  `758110a3…` = fresh emit; eval tests 198 ok; git_dirty false.
- Re-derived here: `awk -F'\t' '!/^#/ && $1!="result"{c[$1]++} END{for(k
  in c) print k, c[k]}' baselines/native-full.tsv` → `PASS 3347`, `FAIL
  246` (total 3593). Negative lane: `baselines/negative-full.tsv` 394
  PASS / 0 FAIL (same awk).
- The first draft of this document was measured at `9343a310` (3528 =
  3283/245; twin `a9a2e2b1…`); every figure below was re-derived at
  `7677865a` after the rebase, and where a section keeps the older
  figure for history it says so.
- Oracle pin: `baselines/go-oracle-pin` = `go1.26.5`; spec pin
  `golang/go @ go1.26.5` = `c19862e5f8…` (`docs/spec-sources.md:15-19`).
- Twin wire pin: `sha256sum baselines/pins/twin-chdriver.wire.json` =
  `758110a3f5a212b8…` (moved by e13-b's 128 `unseq-probe` statements;
  fresh emit at the round-17 train tip `7677865a`; the pre-e13-b pin was
  `a9a2e2b1…` at `9343a310`).
- `e13-b` LANDED in the same train: semantics `2fb7d54d`, audit fix
  rounds `7a5cd534` / `42893297` / `e4d785de`, records `7677865a`; the
  train's step 5a (slow-tier re-certification, set identical, C9
  cleared) landed as `79214ab2` — records only — while this lane's
  second gate ran; the lane was rebased onto it (second snapshot ref
  `refs/snapshots/master-plan-0905-pre-rebase-2`). Every figure in this
  document holds at `79214ab2` (the tree differs from `7677865a` only in
  the certified-set header). Its
  design note is `docs/2026-09-05_e13-b-design.md` on main; where this
  document cites it at `389f4618` (the pre-rebase lane tip) the content
  is the same note.

**Addendum 2026-09-05 ([AGENT], this lane) — the tip moved during the
gate.** The first `scripts/ci --diff` of this lane ran at `9343a310`
while the `e13-b` train landed twelve commits on `main`; per the brief
the lane was rebased (snapshot ref `refs/snapshots/master-plan-0905-
pre-rebase`; clean rebase, records-only commits) and every number in §2
re-derived from the new tree. What changed between the two tips: +65
rows (3528 → 3593; the E13 family, 39 → 56 membership rows), BUG-101/
102/104 now on main (104 entries, 16 open), `ChoiceSite` gains
`unseqPanic` (12 constructors), E13 moves to (a) ENVELOPED and leaves
the honesty-critical list while E2's value axis (BUG-101) and BUG-104
join it, frontier bucket 141 → 137 and post-vintage 61 → 66, twin pin
`a9a2e2b1…` → `758110a3…`. The reconciler's C6 finding this document
caused at `9343a310` (dangling e13-b bug refs) cleared at the rebase.

### 0.3 Status vocabulary (exact; used for every item below)

| word | meaning | must carry |
|---|---|---|
| LANDED | on `main` at or before `7677865a` | the commit SHA |
| IN FLIGHT | branch-complete or under audit, not on main | the branch name |
| RULED | a [USER] decision exists and is recorded | the record pointer (file §/line) |
| PROPOSED | an [AGENT] recommendation with no [USER] ruling | "[AGENT]" and the decision the [USER] would make |
| OWED | a recorded debt from a landed step (no new decision needed) | the note that recorded it |
| BLOCKED-ON-USER | cannot proceed without a named [USER] decision | the decision, stated |

### 0.4 The review agent's entry points

1. `CLAUDE.md` (the charter), then `AGENTS.md` (architecture rules).
2. §1.7 below — the exit-criteria checklist. Each line is testable.
3. §2 — every number with its derivation; re-run each command.
4. §3 — the packages; each has a "what the reviewer should probe" list.
5. §6.3 — the ordered review brief with commands.

The tracked documents this plan indexes (read them, not this summary,
when the two disagree — and file the disagreement): doctrine
`docs/2026-08-11_essence-of-go-doctrine.md`; latitude census
`docs/2026-08-11_latitude-inventory.md`; the reasoning-surface plan
`docs/2026-09-04_reasoning-surface-plan.md` (the C-arc's authoritative
sequence is ITS §5.1 table — this document indexes it, never replaces
it); the design-hygiene arc `docs/2026-09-03_design-hygiene-arc.md`; the
stdlib boundary memo `docs/2026-09-03_stdlib-boundary-design.md` and the
register `docs/stdlib-admission-register.md`; the G6 reflect memo
`docs/2026-09-04_g6-reflect-design.md`; the two ledgers
`docs/language-coverage-ledger.md` and `docs/coverage-ledger.md`; the
corpus structure `docs/coverage-suite-structure.md`; `docs/BUGS.md`;
`TODO.md`; the fidelity decisions `docs/assessment/decisions-2026-08-31.md`;
`docs/2026-08-31_qrow-rulings.md`; `docs/discrepancy-backlog.md`;
`docs/spec-divergence-ledger.md`; `docs/operational-lessons.md`.

---

## 1. What "good" means here

### 1.1 The two top-level goals

[USER] Mike, 2026-09-04, verbatim as relayed by the [AGENT] coordinator
(`CLAUDE.md` "What this repo is"; ruling record
`docs/2026-09-04_reasoning-surface-plan.md` §5.4): «(1) to be a highly
accurate go semantics, and (2) to support reasoning about go using an
iris-lean layer (which we won't build, that's a customer)».

Goal (1) is this repo's product. Goal (2) is served by shipping the
consumer interface the customer needs (`GoLean/Interface.lean`, plan
§1, when it exists) — never by building the reasoning layer here.

### 1.2 The two-bounds doctrine

`docs/2026-08-11_essence-of-go-doctrine.md` (ACCEPTED [USER] 2026-08-12):
the machine is the WEAKEST machine Go permits — every degree of freedom
the spec, memory model and library docs leave open is reified as a
choice on the tape (`ChoiceSite`, `GoLean/GoCore/State.lean:288-298`),
never baked into evaluator recursion. Differential testing against `go
run` at the pinned toolchain establishes the LOWER bound (observed ∈
modeled — membership only; it can never certify width); the spec text,
the memory model, library docs, the deployed-program corpus as de-facto
spec, and cross-implementation observation argue the UPPER bound. The
bug definition: `observed ∉ modeled` is always red, never latitude
(exception channel: a recorded gc DEVIATION from the standard,
`docs/spec-divergence-ledger.md` — L-016 is the one instance). Pins of
latitude are scaffolding that carry a re-envelope obligation
(inventory §7), never a fidelity achievement.

### 1.3 The trusted surface — and nothing else

`CLAUDE.md` "The trusted surface": (1) the interpreter (`GoLean/GoCore/`
— `stepFn` and its drivers) plus the native frontend lowering
(`tools/nativefrontend` + `GoLean/NativeToIR.lean`), validated by the
differential corpus; (2) the differential apparatus — coverage runners,
tracked baselines (`baselines/`), the oracle pin (go1.26.5 exactly), the
re-pin guards. Everything else is untrusted tooling (lane runners,
tracers, diagnosers, censuses). A change to (1) or (2) is a
trust-surface change and needs the full gate and the audit.

### 1.4 Fail closed, fail noisy

`CLAUDE.md` "Doctrine": unknown wire node, unsupported feature,
unclassified case, exhausted budget → an explicit refusal that NAMES ITS
CAUSE at the point of failure. A refusal never counts as a pass; a gate
that cannot run FAILS. The corollary the [USER] added 2026-09-03 (memory
`break-incorrect-behaviour`; applied in `docs/2026-09-05_fr19-bug097-design.md`
preamble): fix and go red rather than preserve wrong or over-wide
behaviour; no compensating shim bodies. And ([USER] 2026-09-04,
`docs/2026-09-04_lower-diagnose.md:18-21`): a refusal shows the whole
picture — every blocker, not the first kill.

### 1.5 Honest measurement

Every differential figure states its scope (full vs partial, cached vs
re-certified), bounds as bounds, numbers derivation-anchored. The
per-row tally is the header `awk` above; red buckets are derived by the
`comm` method of ledger §8b/§8c; the wrong-answer class is the one that
ratchets toward zero (`scripts/check-bugs.sh`, `baselines/untriaged-count`).

### 1.6 The customer and what it needs

The iris-lean layer is a CUSTOMER (§1.1). What it consumes is specified
in `docs/2026-09-04_reasoning-surface-plan.md` §1 (the interface as
signatures + contracts, §1.1-1.14), measured against the current core in
its §2, and reached by the C-arc plan of its §3/§5. The parked reasoning
product (`park/reasoning-2026-08-31` @ `7440bf70`;
`docs/2026-08-31_reasoning-revival-guide.md`) is the evidence of what a
consumer actually used: `Config`/`ExecState`/`Cont`/`Loc`/`GoValue`/
`HeapCell`, `Step`/`Steps`/`StepE`/`StepM`, three heap operations, two
continuation walks, four bridge theorems, `Step.preserves_wf`, the
`*_congr` frame family, `StateWf`/`MachineWf` (plan §0 fact 2). The pin
the customer takes is a SHA whose `GoLean/Interface.lean` matches plan §1
name for name (plan §1.13; gate G-PIN).

### 1.7 What "good" is NOT — and the exit criteria

NOT: proofs in this repo (none; the core is total and sorry-free so the
customer can prove); NOT gc-pinning of latitude presented as fidelity;
NOT shims that make wrong behaviour look right; NOT a model of one
implementation's scheduler.

**Exit criteria for "good as we understand it now"** — a checklist the
reviewer can test. Each line names its test and its current state.

| # | criterion | test | state at 7677865a |
|---|---|---|---|
| E1 | Core is total: no `sorry`/`native_decide`/axiom in `GoLean/`, no `partial` in `GoLean/GoCore/` | `scripts/ci` escape-hatch steps (lines 193, 235, 276) | met (gate green at tip) |
| E2 | Differential lower bound holds on the whole corpus: zero unexplained wrong answers | `scripts/check-bugs.sh` → `wrong-answer 0/0` | met (0/0; 14 unexplained reds are coverage 10 / latitude 4) |
| E3 | Every red is rowed: frontier row, design question, (c)-pin with written reason, or BUGS Cases line | ledger §8 bucket arithmetic 141+9+26+8+61 = 245 | met by arithmetic; the reviewer re-derives it (§2.2) |
| E4 | Every spec section classified | ledger §8 status table: 158 sections, zero unclassified | met (§2.3) |
| E5 | Latitude census is code and matches the mirror | `python3 tools/reconcile-records` check C12; `inductive ChoiceSite` (`State.lean:288-299`) 12 ctors = §0 table 12 rows | met; `file:line` cites in the mirror are stale (§3.D) |
| E6 | No known-≠-oracle deterministic pin without a queued re-envelope obligation or a recorded gc deviation | inventory §10 list {E3, E5, E7, E13, R3} vs §7 queue | met formally; E3/E7/R3 obligations are OPEN debts (§3.D) |
| E7 | Racy programs refuse per run, per go_mem exactly | `scripts/detector-soundness --select in-scope`: HOLE cell 0 | met (364 in-scope rows; HOLE 2 → 0 after BUG-080; §3.D item 6) |
| E8 | Consumer interface exists and matches plan §1 | `GoLean/Interface.lean` present; bridge theorems stated | NOT met — I5 not started (§3.A) |
| E9 | Frontier queue is empty of S-sized sequential rows, or every remaining row has a written profound reason | ledger §4 open rows vs §5.1 | NOT met — 21 open rows (§3.B) |
| E10 | No injected library text in the wire | register `shim=0` | NOT met — 6 fmt shims (§3.C) |
| E11 | Downstream subjects lower end-to-end: raft twin pinned; cedar-go `isAuthorized` drivers reach MATCH | `scripts/check-frontend-pins`; `scripts/cedar-census run` | raft pinned (met); cedar 0 drivers at MATCH (§2.5) |
| E12 | Oracle legs run on cadence: version sweep, 386 static, gotest, grossmith | the four lane scripts | tooling met; cadence PROPOSED, not ruled (§3.E) |
| E13 | Assessment re-run green against the reshaped core | plan §5.2 | NOT met — scheduled after I5 |

"Good as we understand it now" = E1-E13 all met. E1-E7 are the
lower-bound/honesty floor and hold today; E8-E13 are the roadmap.

---

## 2. Where we are (measured)

Every figure: the command or `file:line`, at `7677865a` unless marked.
Numbers this lane could NOT derive are listed in §2.10 and marked
"(not re-derived)" where used.

### 2.1 The baseline tally and its stage breakdown

`awk -F'\t' '!/^#/ && $1!="result"{c[$1]++} END{for(k in c) print k, c[k]}'
baselines/native-full.tsv` → PASS 3347, FAIL 246 (3593). By stage (same
file, `$1,$3`): PASS `-` 3103, confluent 88, membership 121, racy 35; FAIL
frontend-export 198, lean-observation 35, differential 10, confluent 1,
go-observation 1, `lean-observation|differential` 1 (the single
[USER]-ruled stage alternation row, `channels/select-select/beside-loop`,
`docs/coverage-suite-structure.md:508-539`). Negative lane: 394 PASS / 0
FAIL (`baselines/negative-full.tsv`).

The header of `native-full.tsv` is 1337 comment lines above the column
header (line 1338); 32 `# re-pinned:` certification blocks since
2026-09-03 (`grep -c '^# re-pinned:'`). That header is where merge-train
conflicts land (§3.I).

### 2.2 The red buckets (ledger §8, lines 1094-1099 at `7677865a`)

| bucket | reds | derivation the ledger names |
|---|---|---|
| frontier FR-1…FR-31 | 137 | sum of §4 `reds` cells (§3.B lists them; 141 at `9343a310`, −4 when e13-b retired FR-28's A6 refusals into membership) |
| design questions Q-* | 9 | ledger §6 rows |
| (c) profound-reason pins + the `unsafe` marker | 25 + 1 | triage §4 + §5.1 items 1-3 |
| (a)-queued fixes A3/A4/A5/A7 | 8 | triage §3.2 |
| post-vintage arc reds (BUGS Cases lines) | 66 | §8b/§8c `comm` of FAIL ids old vs new, each mapped to a Cases line (61 at `9343a310`; +5 = BUG-101 ×2 + BUG-104 ×3 red-first) |
| total | 246 | 137+9+26+8+66 |

The `comm` method (ledger 1737-1743): `git show <vintage>:baselines/
native-full.tsv | awk '$1=="FAIL"{print $2}' | sort > old; awk … > new;
comm -23 old new; comm -13 old new`. Staleness found at `9343a310` and
still to confirm at the new tip (line numbers are the older tip's): the
reds heading (990) still says "The 196 baseline reds"; the "queue mass"
paragraph (1091-1098) says "19 live arcs … 94 reds" against a frontier
of 137; queue row `5` (427) is not struck although FR-5 is RETIRED.

### 2.3 Language coverage (ledger §8 status table, lines 972-988)

Spec: 158 sections, zero unclassified — covered(A) 30, covered(B) 80,
covered(C) 0, covered(D) 28, frontier 2 (Imaginary_literals,
Complex_numbers — both FR-15), latitude 0 as primary, out-of-language
18. Memory model: 18 sections — covered(B) 9, covered(D) 2, frontier 1
(goexit → Q-GOEXIT), latitude 1 (model → C10), out-of-language 5.

Frontier table (ledger §4, lines 341-373): **31 rows** — 21 open, 6
PARTIALLY CLOSED (FR-4, 22, 23, 24, 25, 28), 1 CLOSED (FR-19), 3
RETIRED/LANDED (FR-5, 8, 27). Reds per class of red: frontier
refusals (the 137 above, all at stage frontend-export or lean-observation
by name); designed reds (BUG-084 ×5 go_mem-only, BUG-100 C6 pin, BUG-102
×6 at the E13 (b) boundary, the 8 address-printing `print` refusals,
R7's 7 default-NaN refusals); latitude pins standing red (R15 zero-size address; E3/E7
deviation rows); post-vintage bugs (BUG-078, 083, 090, 093, 099, 103…).

`docs/coverage-ledger.md` (area × status, 36 rows): 8 active, 25 partial,
2 deferred-nondet, 1 deferred-unsafe, 0 missing.

### 2.4 The standard-library boundary (register machine block; `scripts/check-stdlib-register` green)

`scripts/check-stdlib-register` → source-through=13 (`bytes, cmp,
encoding/binary, errors, internal/bytealg, internal/strconv,
internal/stringslite, math/bits, slices, strconv, strings, unicode,
unicode/utf8`); substitution=5 (bytealg `*_generic.go` twins);
overlay=5 / cap 12; overlay-import=5 / cap 8; intercept=0; primitive=2 /
cap 2 (`float-bits`, `print-output`); **shim=6** (all `fmt`: `Errorf,
Fprint, Fprintf, Sprint, Sprintf, Sprintln`, frozen under D-002);
shadow-type=5 (the `sync/atomic` typed wrappers); init-callee=3
(`os.Getenv`, `os.LookupEnv`, `time.Date`). Library pin
`baselines/stdlib-pin.tsv` (69 lines). Shim history: 20 (freeze) → 14
(slice 1) → 7 (slice 2) → 6 (cmp.Compare retired 2026-09-04,
[USER] «(2) given we have a plan, I think this should be an honest red»,
`docs/stdlib-admission-register.md:263-265`).

### 2.5 Downstream subjects

- **raft**: twin wire pin `a9a2e2b1…` (§0.2), checked by `scripts/
  check-frontend-pins` (ci step 424) — fresh emit = pinned bytes;
  static lowering 691/696 declarations (`docs/2026-09-04_lower-diagnose.md`,
  calibration; not re-derived). W4 stage-2 (tracker differential) is the
  next raft arc (`docs/2026-08-15_raft-master-plan.md:172-178`; memory
  `raft-push-scoping`); no raft lane is live.
- **cedar-go** (`docs/2026-09-03_cedar-go-coverage-census.md`, addenda
  §9-§13): EXPORT-OK **25/34** census cases since FR-4 (§11.2); the 8
  functional drivers refuse AT RUN on per-declaration stubs (FR-14 fmt
  verbs ×4, `io.EOF` ×2, `encoding/json`, `maps.Keys`); 1
  MACHINE-REFUSED (`drv-ext-ipaddr`, `net/netip.Addr` zero value); the
  whole-library `all` case REGRESSED to whole-export refusal on the
  FR-31/BUG-098 guard (§13, lines 999-1005) — an honest red replacing a
  wrong answer. Static: 1443/1569 declarations (92.0%), 965/1086
  funcs+methods (88.9%), 125 refused, export kills 17 decls / 8 of 24
  packages (§13.2). **No cedar driver has reached MATCH or MISMATCH at
  any point** (machine 0/0/0). The blocker table is §3.H.
- **goose imports**: verbatim upstream bodies from `deps/goose` at the
  pinned rev (`scripts/import-goose`), guarded by ci steps 345/447; one
  certified slow-tier set `baselines/certified/imported-goose__channel__
  google-search.certified.tsv`.
- **GOROOT/test** (`docs/2026-09-01_gotest-triage.md`): 2,663 files
  surveyed, 1,013 plain single-file `run` tests = the in-scope slice; at
  `670d3351`: FRONTEND-REFUSED 641, MATCH 331, MACHINE-REFUSED 15, INFRA
  22, MISMATCH 4 (agreement 331/335 = 98.8%); after the `gotest-fixes`
  slice — main `fa589f62`; the report's addendum (:317-323) names the
  lane SHA `f2bc17dd` — 642 / **337** / 13 / 21 / **0**. The four mismatches were all model bugs (BUG-074/075/076 +
  BUG-077/078/079 found alongside), all FIXED. Print-refused files:
  195 (`docs/2026-09-03_stdlib-boundary-design-census.md:474-508`); after
  stdlib slice 3, 120/195 MATCH (`docs/2026-09-04_stdlib-slice-3-design.md:44-45`;
  not re-derived here). The report has NOT been re-run at `7677865a`.

### 2.6 Open bugs and the ratchet

`scripts/check-bugs.sh` → `ok (104 bug(s); pinned cases behave as
claimed)`; backlog 14 unexplained fidelity failures: coverage 10/10,
latitude 4/4, **wrong-answer 0/0**. `grep -c '^## BUG-' docs/BUGS.md` =
104; `- Status: open` 16, `fixed` 88 (the only two words the gate
accepts). The 16 open, by class (§3.G has the table) — the 13 that were
open at `9343a310`: 2 wrong-answer at
a forced point held as red-first pins (BUG-099 runtime-error type
identity; BUG-061 init-order pruning, ruled latitude at L-011); 4
refusals of legal Go (BUG-008, 041, 103, 093); 1 latent Prop-level
unsoundness (BUG-002); 1 apparatus budget (BUG-065); 1 performance
(BUG-090); 1 latitude (BUG-094); 2 designed/guarded (BUG-100 C6 pin,
BUG-098 guard over a wrong-answer class); 1 rendering (BUG-004); plus the three e13-b landed: BUG-101
(wrong-answer at a forced VALUE point, red-first, 2 rows), BUG-102
(designed reds, 6 rows), BUG-104 (wrong-answer — lower-bound violation,
red-first, 5 rows).

The ratchet (`scripts/check-bugs.sh:23-31`, `baselines/untriaged-count:
2-3, 14-17`) counts unexplained FAIL rows at fidelity stages
(`lean-observation, differential, membership, confluent, racy, nondet`)
per disposition class; `wrong-answer` may only go down. **Its blind spot,
stated in the records**: a guard that converts a silent wrong answer into
a `frontend-export` refusal moves the row OUT of the ratchet's filter
(`baselines/untriaged-count:293-299`; `baselines/untriaged-ids:28-29`;
BUG-098 at `docs/BUGS.md:5648-5657, 5678-5680`). The brief for this lane
cited this as "BUG-098 R23"; no `R23` exists in any tracked file (the
fr19-bug097 audit numbering ends at R22) — the record is BUG-098's R4
paragraph at the lines above. §3.G proposes the fix.

### 2.7 The choice tape

`inductive ChoiceSite` (`GoLean/GoCore/State.lean:288-299`): 12
constructors — `mapIter appendSpill l2Entry l2Arrival l4Waiter l1Sched
l5ExitWindow postOp backEdge nilValueMethodText tryLock unseqPanic`
(the last added by e13-b); scheduling subset `{l1Sched, l5ExitWindow,
postOp, backEdge}`. The inventory's §0 mirror has 12 rows; `python3
tools/reconcile-records` check C12 raises no finding (rows =
constructors). Inventory §10 tallies at `7677865a` (its "## 10"
section): (a) ENVELOPED 11 sites / 13 entries; (b) PINNED 17; (b-n)
NARROWED 7 (C7, E8, R3, R4, R5, R7, R13); (c) FORCED the §4 list; (d)
UNKNOWN 6; REFUSED 6 (re-derived by e13-b — the "9 vs 6" discrepancy
of the older tip is gone). Consumption rule
since G-U (LANDED `e58eff5e`/`9cece4e8`, 2026-09-04): pop iff bound ≥ 2,
at every site (the landing record `0cdb15f4` names the lane-local SHA
`9cece4e8`; `e58eff5e` is the same change on main); whole-corpus trace
bijection PASS over 23,016 records
(`docs/2026-09-04_c-arc-gu-design.md` §4). Membership rows: 121 PASS at stage
membership (§2.1; 64 before e13-b); certified sets pinned by `members=`;
sampling budget K=32 on `--diff`, K=80 on `--slow` ([USER] 2026-09-03,
`docs/coverage-suite-structure.md:136-176`).

### 2.8 Oracle pin and legs

Pin `go1.26.5` in `baselines/go-oracle-pin`; enforced by ci step 166 and
by every runner (`scripts/diff-coverage:326-339`, `coverage-negative:
47-60`, `gotest-triage:100-101`, `cedar-census:88-89`, `lower-diagnose:
78-79`, `oracle-version-sweep:120-122`, `oracle-386-static:227-229`).
Legs ([USER] fidelity decision 4, `docs/assessment/decisions-2026-08-31.md`
item 4; report `docs/2026-09-01_oracle-legs.md`): version sweep —
only ONE toolchain on the box, null-validated on a 50-case sample (48
PASS + 2 FAIL = baseline's reds, zero drift), second toolchain NOT run
(operator command handed over :102-110); GOARCH=386 static census — exec
2493 → 2481 both-accept, 12 386-only reject (2 dirs: `strings/
trimspace-repeat/*` ×10, `sync/waitgroup-int32/*` ×2), negative 390/390
both-reject, 0 reason drift; dynamic 386 impossible here (SIGTRAP).
Grossmith campaign 3 (`docs/2026-09-01_grossmith-campaign-3.md`): 39,800
valid judged — 39,796 match, 3 observation-mismatch (all gc-side or
latitude: L-015 third witness; L-016 E5 gc deviation ×2), 1 reference
infra; ZERO machine bugs; first leg was an INFRA failure (ARG_MAX via
TMPDIR length, `docs/operational-lessons.md:206`).

### 2.9 What this week's audits found and fixed

Every lane's pre-merge adversarial audit produced a fix round. `git log
--since=2026-09-03 --format='%h %s' main | grep -i 'wrong answer\|fail-open'`
returns exactly four commits (`7bc0f9ca`, `102f4dae`, `8ddfd6f3`,
`70c0c883`); widening the grep to `wrong-answer\|BUG-098` adds
`3d0dac2a` and `249dc607`. The six, with what each closed:

- `3d0dac2a` BUG-095 + BUG-096 — embedding-interface satisfaction
  (frontend) and shift-count saturation (machine).
- `102f4dae` stdlib-slice-3 fix round — float-bits guard made
  sign-insensitive + `min`/`max` refusal ("wrong answers closed");
  harness split made fail-closed on 4 shapes.
- `8ddfd6f3` fr27-fr28 fix round — `containsInterface` closes the
  map-read wrong answer (a regression on the len/cap path).
- `7bc0f9ca` fr19-bug097 fix round — R1 BLOCKER: `*T` pkgpath follows
  gc's uncommon-section rule; R3 runtime-error type refuses in assert
  texts (BUG-099 filed as the open wrong answer behind it).
- `249dc607` — BUG-098's distinct-name shape ANSWERED WRONG on main (gc
  `false`, main `true`); converted to a named whole-export refusal.
- `70c0c883` lower-diagnose fix round — a crashed frontend had read as
  EXPORT-OK (fail-open, closed); FR-7 phantom removed.

The brief for this lane summarised these as "4 wrong answers at root";
the list above is what the log names — the reviewer should count from
the commits, not from this sentence. Fail-open classes closed this week
(each with its lesson): the tracer's comparator projecting the output
field away on refusal paths (`561f855b`; `docs/operational-lessons.md:
486`); the lower-diagnose one above; the exact-match guard on a two-valued oracle (`operational-lessons.md:
310`, [USER] ruling (a)); timeouts read as verdicts
(`operational-lessons.md:238`); the ARG_MAX cliff (`:206`).

### 2.10 Numbers this lane could not derive (stated, not hidden)

- raft 691/696 static declarations and cedar 974/1085 static — quoted
  from `docs/2026-09-04_lower-diagnose.md`; `scripts/lower-diagnose` was
  not run here (needs the built frontend; lane budget).
- gotest 120/195 print-refused files MATCH — quoted from
  `docs/2026-09-04_stdlib-slice-3-design.md:44-45`; `scripts/gotest-triage`
  not re-run at this tip.
- Session estimates everywhere are [AGENT] guesses anchored to two
  calibration points (plan §3.0: the A-series and B1); they are not
  measurements.
- The 4-wrong-answers count of the brief (§2.9).

---

## 3. Technical packages

Nine packages. For each: goal · current state · numbered work items
(status, size in sessions where a plan table gives one, dependencies,
gate/ruling reference, exit criterion, evidence pointer) · risks · what
the reviewer should probe. "Session" = one worker lane, branch-complete
with gate and audit-ask, ≈ one agent-day (plan §3.0 calibration).

Packages split/merged relative to the brief, with reasons: the brief's
A-I are kept as-is; the atomics/sync line is folded into D (latitude)
because its open items are choice-site and detector questions, not a
library boundary; W7/SpecTec is in F (frontend trust) and again in §4
because only its prep artifact is tracked here.

### 3.A Reasoning surface / the C-arc

**Goal.** Ship `GoLean/Interface.lean` matching plan §1 name for name,
over a core whose representation no longer leaks into consumer proofs
(plan §0 fact 1: the park's `Lifting.lean` broke on `Heap.set`,
`coerceStoredValue` ×131, `typeResolutionFuel` ×335 — theorems about our
representation, not about Go). Then the assessment re-run and the pin
offer. Authoritative sequence: plan §5.1 table; this section updates its
status column to `7677865a`.

**Current state (plan §5.1 rows, updated).**

| # | item | status at 7677865a | evidence |
|---|---|---|---|
| 0 | wave (iii) B2+B3+B8 (+A7 accessor half) | LANDED `1ebd7465` (B2) / `dfe763f9` (B3) / `50e3ea41` (B8), 2026-09-04 — the design note's `91c57c9e`/`cd2a3474`/`2e69fde0` are pre-rebase lane SHAs; train round 13, 5a at `ac45aedd` | `docs/2026-09-04_hygiene-wave3-design.md` |
| 1 | U `consumeAtOne` uniformization (G-U) | LANDED `e58eff5e` (landing record `0cdb15f4`; fix round `fc9bbef1`) | `docs/2026-09-04_c-arc-gu-design.md`, `docs/evidence/2026-09-04_c-arc-gu/` |
| 2 | B4 `Signal` + `Status` (+I2) | LANDED `75d29186` (1/3) + `1a82f305` (2/3+C5) — the design note's `40fd1903`/`165822ef` are the pre-rebase lane SHAs; fix round `561f855b`; `Park` type OWED | `docs/2026-09-05_c-arc-b4-design.md` §7 |
| 3 | C5 `.opDone` → thread boundary flag (G-C5) | LANDED `1a82f305` | same note; `docs/evidence/2026-09-05_c-arc-b4/` |
| 4 | B7 `ProgramCtx`/`Store` (+I1, Platform threading) | PROPOSED-next in the ruled arc; not started | plan §3.0 ("the hinge nobody scheduled") |
| 5 | C1 `Mem` + access trace (+I3, I4) — G-C1 | RULED [USER] 2026-09-04 (plan §5.4); not started | plan §3.C1 |
| 6 | C2 well-founded `TypeEnv` — G-C2 | LANDED `21bb79f7` (records `703bbb03`…`9343a310`, round 17); twin pin moved (a pure permutation of the type entries — 92 per the `21bb79f7` subject, 93 per the note :671; the two records disagree by one) | `docs/2026-09-05_c-arc-c2-design.md`, `docs/evidence/2026-09-05_c-arc-c2/` |
| 7 | B6 `VarId` | PROPOSED (parallel lane); not started | plan §5.1 row 7 |
| 8 | P native method promotion — G-P | RULED [USER] 2026-09-04; not started; needs C1 | plan §3.P |
| 9 | C3 `Cont := List Frame` — G-C3 | RULED; not started; needs B3, B4, P | plan §3.C3 |
| 10 | C4 block-scoped allocation — G-C4 | RULED; not started; needs B6; preserving up to heap iso only | plan §3.C4 |
| 11 | B5 `Chan` module | PROPOSED, optional, any time | plan §5.1 row 11 |
| 12 | I5 `Interface.lean` + bridge theorems | PROPOSED; last | plan §3.I |
| 13 | assessment re-run | PROPOSED; after 12 | plan §5.2 |
| 14 | pin offer — G-PIN | RULED [USER] 2026-09-04 (conditions plan §5.3) | plan §5.3 |

Gate provenance: all nine gates (G-U, G-C5, G-C1, G-C2, G-P, G-C3, G-C4,
G-OUT, G-PIN) RULED [USER] 2026-09-04 as recommended («let's move ahead
with the plan», relayed) and the coordinator's per-gate reading
CONFIRMED [USER] 2026-09-05 («(1) approved», relayed; plan §5.4 second
ruling record, landed `426af905`). Disclosed ordering: G-U and G-OUT
implementations landed before the confirmation arrived (plan §5.4).

**Work items.**

1. **B7 `ProgramCtx`/`Store` split** — PROPOSED-next; 2 sessions;
   depends on wave (iii) (landed); no gate (re-packaging); exit: `Program`
   and `Platform` out of `ExecState`, `htypes` hypotheses deleted, I1's
   five refusal markers gone from the IR (`unsupported` constructors at
   `Syntax.lean:304/319/530`, `Value.lean:202` at this tip — plan §1's
   `:187/202/413/:484` cites predate the A-series; `TypeDef.opaqueDecl`
   → a `ProgramCtx` fact — C2's
   reserved-prefix runtime-error entry moves with it, `c-arc-c2` note §8
   item 3); zero baseline drift; whole-corpus trace byte-identical.
2. **C1 `Mem` module + emitted access trace (I3, I4)** — RULED G-C1; 4-6
   sessions; depends on B7; exit: `accesses_eq_stepAccesses` proved arm
   by arm, `stepAccesses` table retired, any failing arm filed as a
   detector BUG red-first (the gate text); `RacyFine`/`footprintsConflict`
   restated over traces (I4); `step_det_of_choiceFree` (I3);
   `scripts/detector-soundness --select in-scope` re-run with the HOLE
   cell still 0.
3. **B6 `VarId := Nat` locals** — PROPOSED; 2-3 sessions; parallel lane;
   preservation = bijective renaming; twin pin moves; exit: no `String`
   scope keys in the core.
4. **P native method promotion** — RULED G-P; 3-4 sessions; after C1;
   frontend stops synthesizing wrappers (D2: method sets record DECLARED
   methods), core resolves selectors through the embedding chain,
   `Func.wrapper` + four consumers deleted; twin pin moves; BUG-087
   family test becomes chain-depth ≥ 1; detector re-run. Note G6-3:
   reflect T2+ must follow P (the D2 record's meaning changes).
5. **C3 `Cont := List Frame` via `@[match_pattern]` views** — RULED
   G-C3; 3-4 sessions (double if views bite in `fun_cases`, plan §5.5);
   after B4 and P; `Config := Mode × Cont`, `fill` is append;
   definitional preservation; before the pin, never after. Revisit at C3
   whether `Thread.running`'s config-plus-flag becomes a structure
   (`c-arc-b4` §7 item 2) and the frame-exit twins → one
   `FrameEntry`-indexed rule (item 3).
6. **C4 block-scoped allocation** — RULED G-C4; 2 sessions + re-pin;
   after B6; `Stmt.initialization` deleted; preserving UP TO HEAP
   ISOMORPHISM — observations unchanged is the gate; `Loc` trajectories,
   dedup certificates and `repr` pins change and are re-pinned with this
   reason; closure-per-iteration and backward-`goto` classes probed
   first.
7. **B5 `Chan` module** — PROPOSED, optional; 1-2 sessions; equational;
   may follow the pin (changes no §1 name).
8. **I5 `GoLean/Interface.lean` + bridge theorems** — PROPOSED; 2
   sessions; last; `run_ok_iff_stepsM` proved where cheap,
   `run_refusal_free` STATED as target and labelled unproved,
   `EctxLanguage` instance SKETCHED (iris-lean never becomes a
   dependency here; the laws `step_fill`, `step_fill_inv`, `fill_val`
   live here). The two G6 interface deltas must be admitted by the pin:
   `GoValue.typeDesc (idx : TypeIdx)` and `FieldDef.tag : String`
   (`c-arc-c2` §8 owed; G6 §4/§6 G6-3).
9. **Assessment re-run** — 1-2 sessions; after I5; the expected result
   is "unchanged" and that is the claim the re-run certifies (plan
   §5.2); it must ADD the `Accepted`/`run_refusal_free` frontier as a
   graded item.
10. **G-PIN offer** — when plan §5.3's four conditions hold: (a)
    `Interface.lean` matches §1; (b) items 0-10 landed (C4's heap-iso
    re-pin done); (c) re-run green; (d) the plan carries "PINNED @ <sha>".
    BLOCKED-ON-USER at that point (the migration-stage decisions, §3.I).

**Owed from landed steps** (each recorded in the landing note; none
blocks a gate):

- `Park` as a type — `Config.blocked (p : Park)` regrouping the four
  blocked constructors; ~150 mechanical sites across 14 files
  (`c-arc-b4` §7 item 1). Plan §1.3 lists `Park`.
- Bound-irrelevance theorem — `types.WellFounded → i < b → i < b' →
  defaultValueAt types b i = defaultValueAt types b' i` (and the other
  `…At` layers); by strong induction with a `deps`-congruence lemma
  per type layer (`c-arc-c2` §8). Pays at I5.
- `Accepted P` as ONE Prop bundling `typeDefs.WellFounded ∧
  typeDefs.hasReservedPrefix = true` with the decoder's other clauses;
  the `<unknown type index i>` marker class and the
  `$unresolved-type-index.<i>` key belong in the bundle as `∀ i,
  Ty.defined i mentioned ⇒ i < types.size` (`c-arc-c2` §8; audit R10/R1).
  Note: `hasReservedPrefix` compares a long string — never `decide` it.
- The two `Interface.lean` deltas above (`typeDesc`, `FieldDef.tag`).
- `.probeK` traveller arms — OWED from e13-b (LANDED `2fb7d54d`; design
  note §3 and §8): the `unseq-probe` frame `probeK` (Machine.lean)
  admits only expression evaluation, so a `.breaking`/`.continuing`/
  `.returning` traveller at it has no `Step` rule; `stepFn` refuses it
  through the existing `.internal` catch-all rather than explicit
  `.probeK` arms, because every added arm shifts `MachineSound`'s
  positional case tags (three theorems broke on the attempt). Owed:
  explicit arms once C3's `Config := Mode × Cont` makes the case tags
  structural — a concrete instance of why C3 precedes the pin.
- Wave-(iii) residue: `itersNormalized` deletion (216 refs), program-
  text `locSup` deletion (A4), A7 accumulator flip (~110 sites), A11
  `sortSlice` op deletion (`Syntax.lean:424`), `RaceState` canonical
  order, helper-internal `Result` monad, no `stepFn` 4-tuple reshape
  (`docs/2026-09-04_hygiene-wave3-design.md` "Owed onward").
- The GoCore relational-module extraction (split plan, known-owed):
  `Machine`, `MachineSound`, `Multi*` soundness, `NPDRF`, `Race` plus the
  `*Eqb` seam are ruled reasoning-side but interleaved with the
  executable core; extraction is its own slice with full `--diff`
  revalidation, at or before the migration stage. Sequencing note
  ([AGENT]): do it AFTER C1/C3 (U14 in the professor review: "extract
  AFTER U1/U6"), so the extracted modules are the reshaped ones.

**Risks.** (i) B7 is on the critical path and unscheduled by any lane;
every downstream item waits. (ii) C1's arm-by-arm theorem may expose
detector arms that disagree with the table — by the gate each is a
red-first BUG, which is the point, but it can add rows. (iii) C3 cost
uncertainty (plan §5.5). (iv) `run_refusal_free` stays unproved for a
long time; the customer must treat it as a named assumption. (v) The
critical path (iii) → B7 → C1 → P → C3 → I5 → re-run → pin ≈ 17-22
sessions; whole table ≈ 28-38 at 1-3 lanes (plan §5.1). After the pin
every item is a two-repo change.

**Reviewer probes.** Does `git grep -n 'Heap.set\|coerceStoredValue\|
typeResolutionFuel' GoLean/` return nothing? Does `Config` have 10
constructors and `Step` 108 rules (`c-arc-b4` note: 16→10, 141→108)?
Is the whole-corpus consumption trace at the tip byte-identical to the
pre-arc snapshot (`scripts/choice-trace-corpus --dump`, evidence dirs)?
Are the `Park`/bound-irrelevance/`Accepted` owed items in `TODO.md`'s
C-arc section (the b4 note says "rowed at detection")?

### 3.B Language coverage frontier

**Goal.** Every sequential Go construct in the Go 1.26 language either
lowers and runs, or has a written profound reason (ledger §5.1, [USER]:
«the burden of proof is flipped; absence from the queue requires a
written profound reason», ledger 459-460). Queue discipline ([USER],
ledger 381-385): «sequential default = SUPPORT; smallest-diagnosed first;
complex last as the one large arc. Raft-path rows are BOOSTED within
their size class». Re-ranked 2026-08-31 ([USER] fidelity decision 3):
stdlib-boundary work and S items moved ahead; FR-15 explicitly last.

**Current state.** 31 rows (§2.3). Live queue order (ledger 421-450,
struck rows consumed; row `5`/FR-5 is RETIRED but unstruck there and is
omitted here): FR-1, FR-2, FR-3, FR-6, FR-7, FR-9, FR-10,
FR-11, FR-12, FR-13, FR-14, FR-16, FR-17, FR-18, FR-26, FR-31, FR-20,
FR-15. Closed this week: FR-19 (`249dc607`), FR-27 (`6caf9c18`);
partially: FR-4 (`eff1c1a1`), FR-22/23 (`977b92e5`), FR-24 (`ecbbaadd`),
FR-25 (`b146dff2`), FR-28 (`6caf9c18`, then e13-b `2fb7d54d` retired its A6 refusals into
membership).

**Work items** (the plan cells, ledger §4; reds = the row's cell).

1. FR-1 `go` with builtin callee — thunk desugar (gc `gowrap1`); S; 5 reds.
2. FR-2 channel receive in short-circuit RHS — extend E3 conditional
   normalization to `hoistChanRecv`; S; 4 reds; pairs with FR-18.
3. FR-3 pointer-receiver method-expression adapter; S; 2 reds.
4. FR-6 assignment-form range with non-identifier targets — per-
   iteration two-phase target evaluation; 4 reds.
5. FR-7 implicit boxing of tuple components — per-component box at
   comma-ok/tuple stores; 8 reds; BUG-079/BUG-057 history. Reconciler
   C5 finding: FR-7's row cites `=` (ledger:349), which resolves to no
   baseline id — a records nit (§3.I).
6. FR-9 declarations for imported named types — TypeDef emission;
   raft-path; 1 red; BUG-008.
7. FR-10 array-pointer views over slice storage (L2b) — a GoCore
   subarray-view `Loc` or view value; 1 red; **land AFTER C1** (plan
   §4.2) or it is baked into `Mem` twice; user-gate pause class
   (GoCore-touching).
8. FR-11 / FR-20 `goto` — fresh-cell-per-execution (5 reds) / forward
   goto into nested block (1 red); must lower to `Signal` modes
   (`brkTo`/`contTo` class), never a frame-discarding jump (plan §4.2).
9. FR-12 range-over-func iterators — frontend desugar + yield/loop-exit
   protocol; 9 reds; cedar-go priority evidence (§3.H: `Authorize` is
   behind FR-23 → FR-12, 21 functions).
10. FR-13 structural TypeIds for anonymous non-empty structs — decide
    WITH C2's index-keyed `TypeEnv` (plan §4.2); 8 reds; user-gate class.
11. FR-14 / FR-21 stdlib surface and source-through gaps — owned by §3.C.
12. FR-15 complex numbers — softfloat pairs + frontend + constants; 27
    reds; LAST by [USER] direction; adds a `GoValue` constructor.
13. FR-16/17/18 (noodler FG gaps, [USER] direction 3: rowed at
    detection) — defer of builtin (1), self-shadowing define with call
    RHS (1), allocation/splat/method-value in short-circuit RHS (6).
14. FR-26 struct field of unlowerable type kills export — marker
    TypeDef per declaration naming field + cause; also fix the A9
    diagnostic-site defect; 1 red.
15. FR-29 print residuals (BUG-093; owned by §3.C) — 5 reds.
16. FR-30 concurrent print at statement granularity (R18) — 0 reds,
    deliberately unrowed; a semantics item (§3.D).
17. **FR-31 unexported interface method names bare on the wire
    (BUG-098)** — GUARDED 2026-09-05; the fix: qualify by declaring
    PATH via one `methodWireName` helper at every `MethodSig.name`/
    `MethodInfo.name`/dispatch-anchor site, FuncIds unchanged, bare name
    in the `missing method` text; S-M; sequenced after the parallel
    `emit.go` lanes (e13-b is one); exit: the 3 rows PASS, the guard
    retires, cedar-go `x/exp/schema/{ast,resolved}` and the `all` case
    revive.
18. **C6 residue** (ledger §5.1 item 1): function-local defined types as
    a generic TYPE's type arguments — 1 red (`scoping/local-type-
    identity/type-instantiation-refused`, BUG-100 `Expect: FAIL`).
    NARROWED 2026-09-05 by [AGENT] (`fr19-bug097`): the FUNCTION-
    instantiation shape is admitted; the TYPE-instantiation name embeds
    gc's `decl.gen` counter — "impossibility, not backlog"; **the
    narrowing awaits [USER] ratification at the arc gate**
    (BLOCKED-ON-USER, low stakes: ratify or re-open).
19. Generics instantiation shapes generally: FR-27 RETIRED (explicit
    qualified instantiation lowers); FR-23 partial (imported generic
    type in a signature → stubs; the calls unblock with FR-12); the
    stencil quarantine is per-declaration since FR-4. What remains
    un-rowed is whatever the next census finds — the census is
    `scripts/lower-diagnose` (§3.F).

**"Frontier empty" would mean**: ledger §4 has no open row whose reds
are > 0 and no PARTIALLY CLOSED residue; every remaining red is in §5.1
with a written profound reason ratified by the [USER]; the frontier
bucket in §8 is 0 and the `unsafe` marker + (c)-pins are the only
non-BUG reds. The phrase appears nowhere in the ledger today (grep) —
this is the [AGENT] definition; the [USER] may want to ratify it.

**Risks.** Two GoCore-touching rows (FR-10, FR-13) interact with the
C-arc; landing them out of order costs a re-pin. FR-12 is the cedar
authorization path's gate and is M-L. The queue table is stale in three
places (§2.2).

**Reviewer probes.** Re-sum the §4 reds cells (141); confirm every
FAIL id at stage `frontend-export` maps to an FR row or a BUGS Cases
line (`tools/reconcile-records` C4/C5); check that the C6 narrowing is
marked [AGENT] pending ratification in ledger §5.1.

### 3.C Standard library boundary

**Goal.** No text of ours in the wire: every library function is the
pinned GOROOT source lowered through the frontend (source-through),
with the residual `unsafe`/runtime sites handled by byte-checked
overlays or named refusals, and language primitives capped and
[USER]-admitted. Plan of record: `docs/2026-09-03_stdlib-boundary-design.md`
(G1-G9 RULED [USER] 2026-09-03 «(3) agree, go ahead with the plan»,
memo 894-900) + the register `docs/stdlib-admission-register.md` (G8).

**Current state.** §2.4. Slices 1-3 LANDED (slice 1 `9acf0f43` +
ParseUint ruling `75cf7549`; slice 2 `e92285c0`; slice 3 `6a73d02d` +
fix `102f4dae` + re-pin `79ba488c`).
D-002 freeze in force for the 6 fmt shims (`docs/discrepancy-backlog.md`
D-002; review 2026-10-31).

**Work items.**

1. **Slice 4, NARROWED (strconv leaves)** — RULED [USER] 2026-09-05 via
   G6-4 (memo 1159-1170): delete `goleanShimFmtUint/Int/Hex/Bool/
   Quote*` now (real `strconv` source-through replaces them); KEEP the
   verb×kind matrix and the dyn switch until reflect T2; `fmtdesugar.go`
   is INTERIM. Status: PROPOSED-next, not started (the leaves are still
   at `tools/nativefrontend/fmtdesugar.go:1211-1239`). S; exit: the leaf
   renderers gone, rows green.
2. **G6 T1 `reflectlite` facility** — RULED G6-1/G6-2/G6-3 [USER]
   2026-09-05 (G6 memo §6): new register class `facility` (cap 1), ops
   `typeOf, kind, elemTy, comparable, isNil, implements, assignableTo,
   elem, set, len, index`; substitute `internal/reflectlite` at the
   library path pinned by hash; unblocks `errors.Is/As`, `sort.Slice*`.
   2.5-4 sessions (+1 for the class). Depends on C2 (LANDED) — "T1 may
   start now" (`c-arc-c2` §8). Exit: `errors.Is/As` rows green;
   `check-stdlib-register` renders the op list and substitute hash.
3. **G6 T2 read-full** — after G-P (G6-3: method-table reads follow the
   D2 record); 4-5 sessions; unblocks `reflect.DeepEqual` (19 gotest
   files), `binary` read paths, `fmt printValue` minus `%p`.
4. **G6-4 `fmt` source-through over the facility** — RULED (a); after
   T2 AND G7; 4-6 sessions; `fmt` from the pin with one `pp` overlay row
   (`sync.Pool` → `new`), `Print*` via G7's `os.Stdout`; the six shims
   retire; `fmtdesugar.go` deleted — "one `fmt` semantics, not two".
   Exit: register `shim=0`, D-002 closes.
5. **G6 T3 write+construct** — only because G6-5 is ruled (a); 3-4
   sessions + twin pin move (`FieldDef.tag` on the wire).
6. **G6-5 `encoding/json`** — RULED (a), LAST of the sequence; 5-7
   sessions after T3; `FieldDef.tag` with `structTagCompatible`
   tag-blind (a fidelity fix, BUGS Cases line); three `sync` overlay
   rows; `ptrSeen` over `Loc` identity via an opaque `identityKey`.
   G6 totals ≈ 20-27 sessions (G6 memo 776-784) — "a second lane of
   comparable weight" to the C-arc.
7. **G7 `os` primitives** — RULED (b) 2026-09-03 (`os.Exit(n)`,
   `os.Stdout`/`os.Stderr` as writers onto the output buffers), NOT
   IMPLEMENTED, no lane. **BLOCKED-ON-USER**: the primitive cap is FULL
   at 2/2 (`stdlibPrimitiveCap = 2`, `stdlibregister.go:40-49`) while
   G8's text said "2 + G7's list if ruled" — admitting the os trio needs
   a cap re-ratification. G6-4 depends on it.
8. **FR-21 named gaps inside source-through packages** — `errors.Is/As`
   (→ T1); `internal/strconv` `FormatFloat/ParseFloat/AppendFloat` (the
   float-bits primitive exists, the deps.go casts are not yet lowered —
   "a later slice"); `slices.Insert/Replace` (`overlaps`);
   `binary.Read/Write` (reflect + FR-24); `bytes.ReadFrom/WriteTo` (io).
9. **FR-29 / BUG-093 print residuals** — floats via source-through
   `internal/strconv.AppendFloat` called FROM the print arm ("a machine
   op calling a library `Func` is a new shape needing its own argument",
   S3 224-227); zero-operand rule; init-phase event fold. M.
10. **Admissions owed by cedar demand** (census §13.3): `maps` (returns
    `iter.Seq` → FR-12), `io` (`io.EOF` value position), `time`
    ("specified primitive vs source-through" undecided, register
    247-248), `net/netip` (specified-primitive question), `hash/fnv`
    (S2 overlay).
11. **Register nits** — overlay-import cap 8 is "[AGENT]-provisional
    pending [USER]" (register 34, 360): BLOCKED-ON-USER (ratify); G3
    anchors cover source-through packages only (widening posed,
    unruled, S3 174-180).

**Disciplines the reviewer should verify hold.** Byte-check overlay:
ONE pure-Go expression for ONE unsafe expression at ONE named site,
`tools/nativefrontend/stdlib-overlay.tsv` is the single source for both
the loader and the register, re-verified against the pinned checkout by
`--stdlib-overlay-check` with no program in hand (register 33, 79-91);
a re-pin that changes the upstream body FAILS rather than diverging.
Every source-through admission carries an init-pure-at-the-pin argument.
Library latitude (G4): gc's realized member recorded as a
version-tracked (b)-pin row in the inventory at admission, reified only
on consumer demand.

**Risks.** BUG-090 (assoc-list heap; Builder/Buffer workloads > ~1 KB
exceed the 30 s budget) — A2 landed a dense heap; the re-measure and the
re-size of the fuzz suites are OWED (BUG-090 plan, BUGS.md 5240-5250).
G6 competes with the C-arc for sessions. `fmt` has TWO semantics until
G6-4 (the frontend specialization and, later, the source-through) — the
memo's own warning.

**Reviewer probes.** `scripts/check-stdlib-register` green; `git grep -n
goleanShim tools/nativefrontend | wc -l` trend; the D-002 entry's shim
count matches the register (6); no `facility` class exists yet in code
(confirm nothing of G6 is claimed landed).

### 3.D Latitude and the choice tape

**Goal.** Every point where Go permits more than one behaviour is (a)
ENVELOPED on the tape, (c) FORCED with a spec citation, or a recorded
(b)/(b-n) pin carrying a re-envelope obligation with a queue position;
racy executions refuse per run exactly where go_mem says they are racy;
the census is code and its mirror is current. Doctrine:
`docs/2026-08-11_essence-of-go-doctrine.md`; census:
`docs/2026-08-11_latitude-inventory.md`.

**Current state.** §2.7. Inventory entries: C1-C12 (concurrency), E1-E14
(evaluation order), R1-R18 (representation), plus the stdlib posture
row; the §0 mirror is the reader's copy of `ChoiceSite`. The
honesty-critical list (inventory §10, lines 2544-2558): **E3, E5, E7,
E13 (type-assertion axis), R3 (escaping path)** — E5 is a (c) FORCED
row on which gc DEVIATES (L-016, [USER] 2026-09-02; no debt of ours);
E13 leaves the list when `e13-b` lands; E3, E7, R3 are open (b)-pin
debts.

**Work items.**

1. **E13 sibling panic order as latitude — option (b)** — RULED [USER]
   2026-09-05 («we should do what the standard supports, and avoid
   over-refusal if we can. That's what (b) means right?», relayed;
   e13-b note §0); LANDED `2fb7d54d` + fix rounds `7a5cd534` /
   `42893297` / `e4d785de` (round-17 train, records `7677865a`). Adds
   site `ChoiceSite.unseqPanic` (the 12th) and `Stmt.unseqProbe`; retires the
   `make`/`len`/`cap` A6 refusals into a membership shape for PROBED
   material; narrowed A6 refusal stays for unprobed shapes (BUG-102
   designed reds); twin pin moved (128 `unseq-probe` statements; main's
   pin `758110a3…`). Landed tally 3593 = 3347/246 (`7677865a`). Exit
   REACHED: inventory E13 heading is (a) ENVELOPED (`unseqPanic`); §10's
   honesty-critical list now reads E2 (value axis, BUG-101's rows), E3,
   E5, E7, R3, BUG-104 (inventory :2823-2830); membership rows 39 → 56
   in the family. Reviewer: confirm register #2's known-≠-gc sentence in
   the doctrine was edited in the same change (the STANDING RULE of
   2026-08-31).
2. **E12/E2 value axis — BUG-101** — LANDED as a red-first row with
   e13-b (`assert-ok-early-len-hoist`, gc `mut\n6` vs the machine's
   conversion panic; second row `slice-value-early-len-hoist`): the
   probe evaluates a panicky operand early but DISCARDS its value, so
   when a sibling call mutates what it read gc's early VALUE differs.
   Fix direction ([AGENT], e13-b BUGS entry): carry the early value into
   the residual as a second VALUE-axis choice — E12's re-envelope
   obligation, a named design gate. **BLOCKED-ON-USER** (gate to pose:
   E12 (a) envelope over the value axis vs keep the (b) pin with the red
   row). E12's F2 sentence (either-order vs interleaving claim,
   `docs/spec-interpretations.md` I-2 scope note, lines 84-91) is still
   owed.
3. **BUG-104 compound-target hoist order** — LANDED red-first with
   e13-b (5 rows; open): `emitReadWriteTarget`/`emitMapCompound` hoist a temp
   whose bounds check panics BEFORE the RHS's ordered events; gc's
   `safeExpr` leaves the read in the residual. Fix = decompose like
   `safeExpr` so the E13 probe covers it; an ENVELOPE, not a pin (the
   spec orders neither). Pre-existing on main `b77f3298`. S-M.
4. **§7 re-envelope queue (outstanding)**: #3 E7 hidden-dependency
   init order — detector LANDED `4113fdb3` (2026-09-01), owed a named `Choices` site
   over conforming orders + the func-value dispatch channel; MODERATE;
   raft exposure (BUG-061 is its L-011 face). #4 R3 `[]byte(s)`
   conversion capacity — append-spill mould, one arm + membership pin;
   LOW cost, "best value-per-cost". #5 E3/E4 unordered-panic axes —
   panic-identity membership envelope or linearization (BUG-032's
   territory); MODERATE. Not in the numbered queue but recorded: E2
   two-point envelope at the call rules (E12/E13 ride it —
   MODERATE-HIGH); R7 NaN payloads (BUG-094; floats design note); R18
   concurrent print order (FR-30; statement-boundary L1 consult or
   output-order latitude at the fold); R15 zero-size address identity
   (may-equal choice or membership {0,1}); R1/R16 a second `Platform`
   instance (`gc386`) — blocked on any 32-bit oracle; C7 wake-path L2
   draw (LOW while the two-leg argument stands); E10 permanent-pin
   candidate.
5. **Interleavings (b-n) sub-axes**: e13-b §6 item 1 — right-of-event
   operands (`f() + a[i]`) realize only the lexical order (a probe per
   panicky operand is the mechanism; cost = pops on panicking rows).
   The general "either-order vs interleaving" question is the I-2
   reading (spec silence licenses interleavings) — a machine that
   admits `unseq` generally is a WIDENING the plan excludes (plan §3.X);
   reopening it is the doctrine's business as an inventory row.
6. **Racy programs / go_mem posture** — RULED: upper-bound claims scope
   to DRF programs ([USER] fidelity decision 1); racy executions refuse
   per run; Q-U4RESIDUAL RULED [USER] 2026-09-02 — option (A), "the race
   detector follows go_mem exactly" (the [AGENT] option wording the
   [USER] ruled; the relayed [USER] quotes are in the appendix of
   `docs/2026-08-31_qrow-rulings.md`, row 9; inventory §8 e13): where
   go_mem and TSan disagree on what a race IS, go_mem wins — `race/gomem-only/*` pinned born-FAIL (BUG-084 ×5, designed
   divergence from the `-race` oracle, never a pass). Measured
   (`docs/2026-09-02_detector-soundness.md`; 364 rows × 10 `-race` runs
   at GOMAXPROCS 1 and 8 vs the enumerator): agree-race 23, agree-DRF
   275→277, HOLE 2→0 (BUG-080 fixed by `AccessKind × Loc`), over-refusal
   1 (O1, by design), uncertified 63→61 (20 deadlock members where gc
   gives no verdict, 7 fatal, 24 frontier, 9 budget, 1 truncated).
   Open: BUG-080 residual (b) — a sync ENTRY access checked before a
   FATAL apply (2 possible-HOLE probes; `TODO.md:410-438`, trust
   surface, S-M); U5 merge-vs-overwrite Release un-lane-able; the
   NPDRF/reduction line (register #5, BUG-065's one row; parked with the
   reasoning product; NPDRF proof investment is a SEPARATE later [USER]
   decision, decision 1).
7. **Atomics** — wave 1 LANDED `1b3796c6` (lane `atomics-w1`; 25 functions + 5 typed
   wrappers; `Stmt.atomicStmt`, zero new sites, `mp-litmus` certifies
   {0,1,11}); wave 2 OPEN (`atomic.Value`, `Bool`, `And*/Or*`, `Pointer`
   family — `unsafe` policy question; `TODO.md:277-297`). Q-ATOMIC
   RULED [USER] 2026-09-02 option A′, owner THIS repo; `FairStream` is
   reasoning-side future work — no `Fair` predicate exists anywhere
   (doctrine register #1 residue (ii), verified 2026-08-31).
8. **Sampling and membership certification** — RULED [USER] 2026-09-03
   (K=32/K=80, alternate plain/`-race`, early stop at `members=` never
   before two draws — «spirit of the ruling», option A); strict-lane
   depth guard RULED («(6) strict-lane, agree», `docs/assessment/
   decisions-2026-08-31.md` addendum :87; `membership-depth.md:452`): 3
   rows → confluent, 5
   scheduling + 15 capacity → `depth=N` (a FINDING: their state graphs
   do not close within 40 GB / 60M work), 16 noodler rows routed. Open:
   P3 pin `members=` on the 10 unpinned membership rows (PROPOSED,
   membership-depth §6); P4 periodic menu-invariant audit DEFERRED
   ([USER] «others: lower priority for now?», `decisions-2026-08-31.md:
   87, 102`); close the 16 `depth=N`
   rows to `confluent` (needs the reduction lane).
9. **Census hygiene** — the §0 mirror's `file:line` cites are stale
   again at this tip (extract: appendSpill `Machine.lean:963` → actual
   1387; l2Entry 2819 → 3788; l4Waiter Multi 1039 → 1379; l1Sched 1153 →
   1503; l2Arrival 853 → 1188; l5ExitWindow 1628 → 2165/2214) — exactly
   the drift inventory lines 96-100 say no gate watches; §10's "REFUSED
   9" vs §5's six items; §9 flag 6 (C7's superseded argument still
   stated in `resumeThread`'s docstring, `applySelect`, a corpus
   comment, the channels note :1798) owed to the next Multi/Machine
   slice. PROPOSED [AGENT]: a reconciler check that the mirror's cites
   resolve to a line containing the named identifier (cheap; report-only
   like C12's siblings).

**What a complete census would be.** Every `ChoiceSite` constructor has
a `canonicalSlot0` row, a consult in `seqConsumption`/`poolConsumption`,
an in-situ envelope statement (`stepFn_consumption_*`) and an inventory
entry (State.lean:215-224 docstring); every (b)/(b-n) row has either a
§7 queue position or a permanent-pin ruling; the (d) UNKNOWN set (U-2
L4 ⊆ L1 theorem, U-4 overlapping copy, U-5 granularity ledger, U-7
version-pin firing) is empty or ruled; E12's F2 sentence and E13's
unprobed operand kinds (div-by-zero, slice-to-array, nil-map write, nil
deref vs sibling calls — "NOT claimed by this entry", inventory
1473-1478) are censused. None of that is a gate today.

**Risks.** The inventory is 2,631 lines of prose whose numbers drift
between sweeps; only C12 (row count) is mechanised. E13's landing is the
largest tape change since W3.2 and it lands with a twin pin move and
128 probe statements in the raft wire — the trace bijection and the
membership certification are the checks.

**Reviewer probes.** `grep -c '^| ' `-style re-count of the (a)/(b)/
(b-n)/(c)/(d)/REFUSED headings against §10's tallies; `python3
tools/reconcile-records` C12; for each §10 honesty-critical row, find
its §7 position or its L-entry; confirm no row in `Corpus/` at lane
`membership` lacks `width=`/`members=` where the structure doc says
they are required.

### 3.E Differential apparatus and measurement

**Goal.** The lower bound is measured honestly, cheaply, and on a
cadence: every corpus row compared under the pinned oracle; latitude
rows certified by enumeration and sampled by draws; the oracle probed
from several legs; the apparatus itself unable to say PASS when it did
not decide. Structure: `docs/coverage-suite-structure.md`.

**Current state.** Corpus `Corpus/coverage/exec/<area>/<case>/{main.go,
cases.tsv}` (+ `negative/compile`), lanes `strict`/`membership`/
`confluent`/`racy`, params `width sites cap work members depth`;
`samples=` RETIRED and refused by name. Gate: `scripts/ci` (steps at
§6.3), `--diff` runs the full native corpus, `--slow` additionally
re-certifies `tier=slow` rows (K=80). Stage alternation: ONE row,
[USER] ruling (a) 2026-09-03, `scripts/check-alternation-survival` in
the re-pin guard. Strict-lane depth guard LANDED `82f74922` (lane `strict-routing`);
sampling budget LANDED `f98d4919` (lane `sampling-budget`; the
two-draw floor as ruled). Step 5a (slow-tier re-cert
after any train touching `wire.go`/`NativeToIR.lean`; [USER] 2026-09-04
«Yeah, that make sense, let's adopt that», `operational-lessons.md:
435-484`) ran at rounds 13/14/15 (`ac45aedd`, `8fce7625`, `076f5eec`).
Reconciler C9 at `7677865a` said the wire schema had moved after the
last certification (6 commits, incl. `21bb79f7`, `7bc0f9ca`, `249dc607`
and e13-b's) — the round-17 step 5a re-certification then LANDED as
`79214ab2` (set identical, header refreshed, C9 cleared).
Reconciler `tools/reconcile-records`: REPORT-ONLY ci step (969); 2
MEDIUM findings at `79214ab2` (C13, C5). At `9343a310` this document had added a fourth (C6:
its `BUG-101/102/104` references had no entry on main); it cleared at
the rebase.

**Tracer completeness / driver agreement.** `golean choice-trace`
(`GoLean/ChoiceTrace.lean`, observation-only, outside the core) compares
the engine and the enumerator per (row, stream): status + observation
hash + per-consumption labels; menu-invariant validator 62,048
consumptions / 0 violations (membership-depth §3). The fail-open found
and fixed this week: refusal-path output projected away (`561f855b`).
Guard failing to run (timeout, kill, tracer violation, driver
disagreement, empty stream, < 4 reports) = `nondet` FAIL, never a pass
(structure 272-275).

**Work items.**

1. **Step 5a at the round-17/e13-b train tip** — LANDED `79214ab2`
   (set identical; the standing rule: certified set identical or a
   FINDING, never a re-pin; `CLAUDE.md` 5a). Nothing owed here at this
   tip.
2. **Periodic legs cadence** — PROPOSED [AGENT] in each report, not
   RULED (the [USER]'s 2026-09-03 «others: lower priority for now?»,
   `docs/assessment/decisions-2026-08-31.md:87, 102`, deferred them): gotest triage nightly-class + on fragment widening /
   eval-order change / oracle re-pin (`gotest-triage.md:291-296`);
   grossmith weekly 20k leg (~18-30 min), full two-leg per frontier
   widening, one leg per pin move (§8 of its report); oracle version
   sweep at each Go point release and before any pin move; 386 static
   per corpus-growth arc or nightly (~4 min); P4 menu-invariant audit.
   BLOCKED-ON-USER: pick the cadence (or rule "on demand").
3. **Second toolchain for the version sweep** — the box has one; the
   operator command is in `oracle-legs.md:102-110`. BLOCKED-ON-USER
   (machine-global install — never by an agent).
4. **Tag the 12 386-only-reject ids** (`widths`/`width64-only`) and add
   them to inventory R1; exclusion list for a future 32-bit lane
   (`oracle-legs.md:234-258`). S.
5. **Grossmith**: harden the `diff-coverage:1370` fan-out (trusted
   surface — recommended, not done); add `fatal`/`fuel-out` to the
   external adapter's status sets; the E13 string-slice axis probe row
   owed; L-016 upstream filing pending a P5 policy ([USER]: «record in
   our gc bug backlog», decision 0.12). Widening ladder (report §7):
   non-observable defer form → pointers → floats → stdlib narrow slice →
   generics → concurrency.
6. **gotest extensions** (report 291-296): statement-position print/
   println; the 127 `rundir` multi-file tests; the 675 `errorcheck`
   files as a frontend-refusal-vs-gc-diagnostic lane. Also: re-run at
   `7677865a` (the report is at `fa589f62`/`f2bc17dd`).
7. **Noodler standing persona** ([USER] 2026-09-03: probe rows are
   always rolled in): 563 rows / 90 packages landed; next probes
   (report §9): autogenerated-wrapper texts, systematic `unsup(...)`
   sweep (~25 of ~190 covered), multi-package, panic payload rendering,
   select-with-select/Cond/TryLock. Cadence: PROPOSED — one noodler lane
   per frontier widening.
8. **Reconciler additions** — C15 bare `R\d+` latitude cites resolve to
   inventory headings (`TODO.md:113-118`, owed from stdlib-slice-3
   audit); the mirror-cite check (§3.D item 9); clear C5 (FR-7 `=`) and
   C13 (78 doc sites off the go1.26.5 pin, 60 in the scheduling
   dossier) as records nits.
9. **Apparatus edges recorded, not fixed**: BUG-065 (worker-pool
   enumeration > 9.5M nodes; the reduction lane); the tracer's one
   ERROR row `arrays/materialization-budget/over-budget` (BUG-078 decode
   refusal — cannot run, not a mismatch); tracer wall budget
   `LEAN_TRACE_TIMEOUT_SECONDS` = 8 × `LEAN_TIMEOUT_SECONDS`.

**Risks.** Cached certification going stale silently was the C9 lesson;
it is now report-only — a train that forgets 5a is caught by the
reconciler note, not by a red. One box, one toolchain: the version
sweep is a null test until a second toolchain exists.

**Reviewer probes.** Run `python3 tools/reconcile-records` and read C9;
run `scripts/check-alternation-survival`; confirm `samples=` refuses;
pick three membership rows and re-derive `members=` from
`golean coverage-observations`; confirm the gate tail's `RESULT` line
appears only after every step and that a killed step names itself.

### 3.F Frontend trust

**Goal.** The lowering (`tools/nativefrontend` + `GoLean/NativeToIR.lean`)
is trusted only as far as the differential exercises it, and every
place it decides something is either fail-closed by name or on the road
to translation validation. Rule of record: identity is the wire key,
display is gc's rendering, the wire carries both, the machine decides by
identity only (`docs/2026-09-05_fr19-bug097-design.md` §0).

**Current state.** Per-declaration quarantine (FR-4: stubs refuse AT RUN
by name, the export survives); wire integrity checks added this week
(`7bc0f9ca`: emitter+decoder refusal tests, `program.types` collision
check, record-less package refuses, `PathToPrefix` key-path guard);
determinism — the frontend's typeDefs dependency order self-checks (C2);
twin-pin discipline: `scripts/check-frontend-pins` compares a FRESH emit
over the raft twin assembly byte-for-byte with `baselines/pins/
twin-chdriver.wire.json`; when two merged branches both moved the pin,
the pin is a fresh emit from the MERGED frontend, never a merge result
(`c-arc-c2` note §7, :555, :669; pin history chain in the script header
:29-122). `scripts/lower-diagnose` (LANDED `8c1a7896`, landing `aceb0dcb`;
report-only, ci runs its tests): dynamic first refusal + static census over every declaration
against three supply tables; `DIAGNOSTIC — NOT A LOWERING` on every
artifact; 64 cause rows in `tools/lowerdiag/causes.tsv` at this tip (52
at the report's vintage), 325/341 `unsup` formats classified.

**Work items.**

1. **FR-31 path-qualified unexported method names** — §3.B item 17
   (the one frontend-wide mechanical change; after e13-b lands).
2. **lower-diagnose follow-ups** (`TODO.md:128-153`): flip the
   `global-type-unlowerable` cause from pending → rowed now that
   `fr22-fr23` landed (the gate FAILS as STALE otherwise — verify at
   the tip); the static pass's blind spots disclosed per run; 16
   unclassified `unsup` formats; re-derive the cedar census §3.4 numbers
   from `--json`.
3. **Decoder hardening** — `sync-op`/`atomic-op` nodes with an absent
   `resultTypes` key (`TODO.md:329-333`, F5). S.
4. **W7 SpecTec-Go / translation validation** — the route of record
   (`docs/roadmap.md:373-407`, added 2026-08-20 by Mike): per-program
   simulation certificates (spectec-AST semantics ≃ GoCore semantics of
   the emitted wire, checked in Lean per corpus case) rather than a
   verified re-implemented elaborator; the tool is EXTERNAL (Mike's Lean
   SpecTec). Tracked here: the prep census
   `docs/2026-08-21_w7-desugar-inventory.md` — 249 rows of lowering
   decisions, each a future proof obligation, five obligation kinds (+
   K2m; 13 K2 latitude rows are MEMBERSHIP claims, never gc-equality),
   a proposed certificate order (if-init hoisting → comma-ok →
   shadow-capture), §12 open design questions, and six holes (two were
   live silent wrong answers, H-a/H-d, since fixed — BUG-057/058 era).
   Status: the census is LANDED; nothing else of W7 is in this repo
   (no spectec source, no certificate checker). §4 item 9 discusses the
   decomposition. The 249 anchors are commit-qualified to `e3187410`
   and have drifted ~+91 lines — a re-anchor is owed before any
   certificate work.
5. **Twin pin ownership** — `twin-chdriver`'s Lean consumer
   (`TwinProgram.lean`) is parked with the reasoning product; on main
   the twin is exercised only by the pin (`TODO.md:167-170`). Decide at
   the migration stage whether the twin driver stays here.
6. **Spec pin third leg** — the corpus-side `go.mod` `go` directive as
   the third pin (spec text · oracle · corpus language version) does
   not yet exist (`docs/spec-sources.md:21-25`). S.

**Risks.** Two parallel lanes editing `emit.go` is the standing reason
FR-31 waits; the frontend is where every recent silent wrong answer
lived (roadmap W7 §), and the pin exercises one subject (raft). The
lower-diagnose tables are a second description of the frontend that
must be kept set-equal by tests (they are, `go test ./tools/lowerdiag`).

**Reviewer probes.** `scripts/check-frontend-pins` at the tip; `GO111MODULE
=off go run ./tools/nativefrontend --dir <twin> --out x.json` twice →
identical bytes (determinism); `go test ./tools/nativefrontend
./tools/lowerdiag`; pick three `unsup(` sites in `emit.go` and confirm
each has a `causes.tsv` row with an FR id.

### 3.G Bug backlog

**Goal.** `wrong-answer 0/0` stays true AND means what it says; every
open BUG has a class, a plan and a lane or a queue slot; nothing leaves
the ratchet's view by becoming a refusal.

**The 13 entries open before e13-b landed** (`docs/BUGS.md` at `9343a310`; line = entry
start; class per the entry's own tag where it has one, else [AGENT]).

| BUG | line | class | what | plan | lane / slot |
|---|---|---|---|---|---|
| 002 | 2804 | latent unsoundness (Prop relation) | expression-step atomicity coarser than Go | small-step expression machine (likely) — the concurrency-granularity arc | TODO backlog (re-homed [USER] 2026-08-31 decision 6); Q-ATOMICITY held |
| 004 | 2673 | rendering: 3 (c)-pins + 1 queued | panic abort-line rendering (eface identity, `preprintpanics`, multi-line payload) | item 3 `panic-newline-abort` = mini-slice A7; items 1/4 ratified pins under R-1 | TODO re-homed obligations |
| 008 | 2385 | refusal of legal Go | imported named types have no wire TypeDef → map-key hash precheck refuses | emit real declarations for imported non-interface named types (FR-9's plan) | none; FR-9 queue 9 |
| 041 | 981 | over-refusal (NARROWED 2026-09-02) | detector records whole-cell reads for dynamic-index array reads | option (B) deferred-footprint recording; re-open trigger = a real target | Q-RACEPATH ruled; Tier-4 detector lane |
| 061 | 37 | init-order (L-011 latitude) | staticinit pruning under-approximates gc's | mini-staticinit predicate for 10/11 flavours; `callinit` needs a ruling at L-011 | none — **BLOCKED-ON-USER** (L-011 ruling) |
| 065 | 3448 | apparatus budget (1 row) | `goroutines/worker-pool/sum` exceeds the dedup budget | reduction/DPOR lane (NPDRF slice 5) or a per-row ruling | reduction lane parked with reasoning |
| 090 | 5198 | PERFORMANCE | assoc-list heap O(live cells) per write (A2 landed the dense heap) | re-measure, re-size fuzz, re-expect `repeat-bound-refused` | OWED to the hygiene arc's follow-up |
| 093 | 5336 | coverage | print residuals (float/complex, zero-operand, `$pkginit`, address kinds) | FR-29 (queue 29, M) | `stdlib-slice-3` successor |
| 094 | 5383 | latitude | `Float64bits` of canonical NaN refuses (R7) | platform-faithful NaN rule or (a) envelope over payloads | floats design note; R7 |
| 098 | 5623 | wrong-answer class held as refusal | unexported method names bare on the wire | FR-31 `methodWireName` | queue 31; after e13-b |
| 099 | 5694 | wrong-answer (observed row) | one synthetic `$runtime.Error` type for every recovered runtime error | model gc's concrete runtime-error TypeIds + payloads; per-fault probes | **unowned** |
| 100 | 5743 | designed (c)-pin | C6: function-local type as generic TYPE argument | none — retires only by [USER] re-ruling of ledger §5.1 item 1 | `fr19-bug097` (ratification pending) |
| 103 | 5767 | refusal of legal Go (machine) | `convertValueToTy` lacks the array-target arm | one arm normalizing an `.array` copy; own slice, full run | C-arc C2 audit; three-bug lane (§5) |

Landed with e13-b (`7677865a`; the table above is the 13 of the older
tip — these three make 16 open):

| BUG | class | what | plan | lane / slot |
|---|---|---|---|---|
| 101 | wrong-answer at a forced VALUE point (red-first, 2 rows) | the E13 probe evaluates a panicky operand early but discards its value; a mutating sibling call makes gc's early value differ | carry the early value into the residual as a VALUE-axis choice — E2/E12's obligation, a design gate | **BLOCKED-ON-USER** (§3.D item 2) |
| 102 | designed reds (6 rows) | the narrowed A6 guard and the structural-allocation refusal at the E13 (b) boundary | retire as probes widen (right-of-event operands, compound-call targets) | e13-b successor |
| 104 | wrong-answer, lower-bound violation (red-first, 5 rows) | compound-target address/key temp panics before the RHS's ordered events | `safeExpr`-style decomposition so the probe covers it | three-bug lane (§5.2) |

(e13-b renumbered its own 103 → 104 so the two lanes' entries coexist.)

The untriaged backlog (14 rows, `baselines/untriaged-ids`): 10 coverage,
4 latitude, 0 wrong-answer — each id listed with its disposition; the
ceilings in `untriaged-count` may only go down.

**The ratchet's blind spot and the proposed fix.** Stated in §2.6. The
class of "guard converted a silent wrong answer into a `frontend-export`
refusal" is today visible only as prose in a BUG entry (BUG-098) and as
a warning in `untriaged-count:293-299`. PROPOSED [AGENT]: (i) a
`Guarded-wrong-answer: yes` marker line in the BUGS entry format,
parsed by `scripts/check-bugs.sh` into a THIRD reported count beside
`wrong-answer` («guarded wrong-answer classes: N, each with an FR row»),
so the number is on the gate's tail rather than in prose; (ii) the
reconciler checks that every such entry names an FR row whose plan is
the fix. Neither weakens a gate (report-only additions). Decision
needed from the [USER]: adopt the marker or rule the prose sufficient.

**Reviewer probes.** `scripts/check-bugs.sh --list`; for each open
entry, confirm its Cases rows are FAIL in the baseline (the script does
this) and that the plan sentence names a lane or a queue slot; grep
`docs/BUGS.md` for `wrong` inside open entries with `Pinned-by: none`
(the blind-spot shape).

### 3.H Downstream subjects

**Goal.** Real programs, lowered whole and compared whole: the raft
twin (pinned) and its tracker/log/step-function differential (W4); the
cedar-go authorizer to the point where the FIRST downstream proof
(`cedarGo_refines`, plan §4.4) has a program to be about; the goose
imports as verbatim upstream fixtures.

**raft.** Twin pinned (§2.5). Next arc: W4 stage 2 — Tracker →
`log_unstable`/`MemoryStorage` → the `raft.go` step function, each
differentially validated, stage 4 replaying etcd's datadriven traces
(`docs/2026-08-15_raft-master-plan.md:172-178`); the W4.3 handoff
(`docs/raft-w43-log.md:1305`) lists the W4.5 obligations. Needs from
A-F: FR-9 (imported named types, raft-path, BUG-008); E7's re-envelope
(init order — BUG-061 is raft's `staticinit` shape); the init-order
deviation pin `baselines/pins/hidden-dep-order.observation.json` stays
red by design until then. No lane live; the [USER] said 2026-09-03 «we're
not running Raft right now» (register 136-139) — restart is a [USER]
call.

**cedar-go + cedar-access-control-for-k8s.** Refinement target
(plan §4.4, lines 1496-1562): `cedarGo_refines` — `run P main (encode
req es ps) fuel ch = .obs (.ok r) → decode r = some (isAuthorized req es
ps)`, no terminal, no refusal, plus `cedarGo_total`; `decode` quotients
`determiningPolicies`/`erroringPolicies` to SETS (E9 map-order latitude —
`order_and_dup_independent` does NOT transfer, census §7 567-577). What
the proof consumes, in order: `run_ok_iff_stepsM` + `execProg_single_eq_
execStmt`; `step_det_of_choiceFree` (deterministic except `mapIter`);
`fill`/`step_fill_inv` (C3 + B4); `Mem.load_after_disjoint_store` under
`own_struct`/`own_map` (C1 — "the refinement's real work"); `Accepted P`
decidable + `run_refusal_free`. NOT needed: `Fair`, B5, `StepM` pairing,
`Platform` parametricity. And plan §4.4's own sentence: «The program
must EXPORT first … the refinement is the SECOND thing after export».
The k8s authorizer's cedar-go-only subset is one package
`internal/schema` (36/38 static); the Rust `kubernetes-cedar-authorizer`
is out of scope (census §6-7).

Blocker table at census §13 (what still stops the drivers), with owner:

| blocker | scale | owner |
|---|---|---|
| FR-31/BUG-098 guard | `all` whole-export refused; `x/exp/schema/{ast,resolved}` + 6 inheriting (8/24 pkgs) | §3.B item 17 |
| `encoding/json` Marshal/Unmarshal | 62 decls / 32 sole — heads the per-decl table | G6-5 (§3.C) |
| `iter.Seq` / range-over-func | 21 functions incl. `Authorize` | FR-12 (§3.B) |
| `fmt` verbs (`Sprintf`/`Errorf`) | 4 drivers refuse at run | G6-4 / narrowed slice 4 (§3.C) |
| `io.EOF` value position; `maps.Keys` | 2 drivers; 34 incidences | `io`/`maps` admissions (§3.C item 10) |
| `net/netip.Addr` zero value | 1 driver MACHINE-REFUSED | specified-primitive question (§3.C) |
| `errors.Is/As` | 10 decls | G6 T1 |
| `time` | 21 incidences | primitive-vs-source-through question |
| FR-13 anonymous struct; `context`; `goto` | 3-5 fns; 4; 1 | §3.B |

Path to the first MATCH ([AGENT] reading of census §13.3): FR-31 fix
revives `all` and the two schema packages; then T1 (`errors.Is/As`) and
the narrowed slice 4 unblock the simplest functional drivers; the
authorization path itself waits on FR-12. Nothing here is on a lane.

**goose imports.** Verbatim bodies at the pinned `deps/goose` rev; ci
steps 345/447 guard staleness and the importer's self-test. Needs from
A-F: only that the slow-tier certified set stays identical (step 5a).

**Reviewer probes.** `scripts/cedar-census run` and compare with §13's
table; `scripts/check-frontend-pins`; `scripts/check-imported-goose`.

### 3.I Process and infrastructure

**Goal.** The protocol that makes the rest checkable: branches in
worktrees, gate before commit, unconditional audit ask, ff-only merges,
sign-off at the moment of merge and push, records with provenance.

**Current state (rules of record).** Merge protocol `CLAUDE.md` steps
1-6 + 5a; audit protocol (the ask is unconditional; scope/waiver the
[USER]'s); worktrees under `.claude/worktrees/<lane>`, `deps/` via
`scripts/setup-deps --from`; every lake/lean/ci via `scripts/capped`
(cgroup `MemoryMax`; `lean -M`/`prlimit` do NOT work —
`operational-lessons.md:9,23`); box-wide build lock; scratch never in
`/tmp` (incident 2026-09-04 destroyed evidence copies, `:154`);
background polls die at ~1 h (memory `background-task-hour-cap` — park
lanes with a HANDOFF.md); never kill by pattern (noodler report §7,
`:277-289`; memory `never-kill-by-pattern`); [AGENT]/[USER] provenance
on every logged decision, relayed quotes cited as relayed (U0
convention); snapshot refs before risky git ops.

**Work items.**

1. **Baseline-header narrative** — the `native-full.tsv` header is 1244
   comment lines / 28 re-pin blocks (§2.1); every merge train
   reconciles it by hand (the round-17 commit message's "records only;
   the tree is otherwise byte-identical" is that cost made visible).
   PROPOSED [AGENT]: move the narrative to a tracked
   `baselines/native-full.log.md` (append-only, one block per re-pin),
   leaving the header as the title line + `# cases: N (P PASS / F FAIL)`
   + the awk line; the reconciler's C1H keeps checking header vs data.
   No tracked doc proposes this today (grep: zero hits for "narrative out
   of the header"); it is this plan's proposal. BLOCKED-ON-USER (adopt or
   decline). Cost S; risk none to the gate (the guard reads data rows).
2. **Records nits** — reconciler C5 (FR-7 cites `=`, ledger:349), C13
   (78 doc sites off the pin; 60 in the scheduling dossier), the three
   ledger staleness spots (§2.2), `TODO.md`'s hygiene checkboxes (32-35)
   stale versus the arc doc, `TODO.md:436-438` still calling
   Q-U4RESIDUAL open (ruled 2026-09-02), `coverage-suite-structure.md`'s Gobra-era
   sentences (200-201, 399-401). One records lane; S.
3. **`architecture.md` / `roadmap.md` semantics rewrite** — OWED since
   the split (split plan "Deferred"); low priority; roadmap §W7 is the
   one live section.
4. **Migration-stage decisions** — BLOCKED-ON-USER (split plan
   "Deferred to the migration stage"): new repo name/location
   ([AGENT] working name `golean-logic`, not chosen); dependency
   mechanism (recommended: pinned git require, local remote until push
   authorized); history strategy (recommended: full clone so every SHA
   resolves); whether `raft-proof-campaign` lands or migrates raw. Plus
   the GoCore relational extraction slice (§3.A owed) at or before it.
5. **Decay dates** — RULED [USER] 2026-08-31 (decision 7): every
   set-aside carries an expiry; D-001 review 2026-11-30, D-002
   2026-10-31; the reconciler surfaces expired entries report-only.
6. **Memory hygiene** — the auto-memory index carries rules that are NOT
   in tracked docs (background hour cap; never-kill-by-pattern lives
   only in the noodler report). PROPOSED [AGENT]: add both to
   `operational-lessons.md` so the review agent (which has no memory)
   can find them. S; records only.

**Reviewer probes.** `git log --merges --oneline 7440bf70..main | wc -l`
is 0 (ff-only since the split; the 10 merge commits in main's history
all predate `7440bf70`); every commit touching `GoLean/GoCore` or `tools/nativefrontend`
since 2026-09-03 has a design note + evidence dir + a gate tail with
`git_dirty=false`; `scripts/capped` wraps every lake invocation in
`scripts/ci`.

---

## 4. Broader goals not yet decomposed

Each entry: what is known (with pointers), what a decomposition would
need, in/out of the charter, and the [USER] decision needed. Every
recommendation here is PROPOSED [AGENT]; none is a ruling.

1. **The concurrency/memory model beyond report-and-terminate (racy
   limited outcomes; weak memory; go_mem completeness).** Known: racy
   executions refuse per run; upper-bound claims scope to DRF ([USER]
   decision 1, ground = cost + no differential oracle, NOT "undefined by
   Go"); mem#restrictions' limited-outcomes stance (word-sized racy
   reads see actually-written values, no OOTA) is Go's promise and is
   deliberately UNMODELED (doctrine register #4; inventory §8 e13 (ii)).
   Decomposition would need: a value-branch racy semantics (a bounded
   choice over actually-written values per racy read — a new site), a
   litmus corpus with NO `go run` oracle (only `-race` halts), and an
   argument that the OOTA frontier is drawn where plmm draws it.
   Charter: IN for the doctrine ("all latitude included"), OUT of
   product scope by the standing ruling. Decision: keep OUT until a
   consumer asks; re-pose when the NPDRF proof investment is decided.
2. **Runtime features: GC observability, finalizers, scheduler fairness,
   Goexit, timers.** Known: fairness is a hypothesis on the chosen sequence, not a machine
   constraint ([USER] 2026-09-02 verbatim in the doctrine's "Scheduling
   and fairness" paragraph: «Fairness is an assumption about the
   sequences that are chosen»); `Goexit` is the memory model's one
   frontier section (Q-GOEXIT held, `TODO.md:359-362`); GC-dependent
   behaviour is out of scope by the stdlib memo (648-660); `runtime.GC/
   Gosched` deferred at G7. Decomposition: Goexit as a terminal class
   (S-M, a `Signal`-class mode after B4); timers/`time.Sleep` as a
   scheduling-point-only op (no clock) — a latitude row; finalizers and
   GC observability OUT (no portable semantics). Decision: rule Goexit
   in (recommended) and the rest out with a written reason.
3. **`unsafe`/`reflect` exclusion boundary.** Known: `unsafe` is
   out-of-language with visible marker rows (ledger §5.1 item 2;
   register #6 condition — pointer equality is the only address
   observation); `reflect` is entering as a layout-free FACILITY (G6,
   RULED), with a permanent excluded list (`MakeFunc`, `StructOf`,
   `Value.Pointer`, `Size/Align/Offset`, …). Decomposition: none owed —
   the boundary is drawn and ruled; what is open is whether
   `unsafe.Pointer` round-trips WITHOUT arithmetic (the atomics
   `Pointer` family question, `TODO.md:277-297`) are admissible as
   opaque identity — a latitude row. Decision: rule the `Pointer` family
   at atomics wave 2.
4. **cgo.** Known: out of scope by the memo (cgo/linkname/asm); no
   census. Decomposition would need a foreign-call boundary as a refusal
   class (already the effect) — nothing more unless a subject needs it.
   Charter: OUT. Decision: confirm OUT (no cost).
5. **Full generics: instantiation at local types (C6), method sets of
   type parameters, `comparable` at run time.** Known: C6 is an
   impossibility pin pending ratification (§3.B item 18); FR-23/FR-27
   done or partial; type sets decided by `Ty.eqb`/`structTagCompatible`.
   Decomposition would need a census of generic shapes in the corpus
   and cedar (lower-diagnose `--tsv` gives it) and a decision whether
   the frontend keeps gc's stencil naming (current) or the core gets
   its own instantiation identity (a §1.1 type-identity change — WITH
   C2's index-keyed table). Decision: ratify the C6 narrowing; commission
   the census only if a subject hits it.
6. **Platform parameterization (GOARCH/GOOS beyond amd64 linux).**
   Known: `Platform` record with one instantiation (A5; R1 int width, R16
   `maxAlloc`, gc layout constants); the 386 static census exists;
   dynamic 386 impossible on this box; a `gc386` instance is blocked on
   any 32-bit oracle (inventory §7 below-the-line). Decomposition: a
   second `Platform` instance + a 32-bit oracle host + a `widths`-tagged
   sub-corpus (89 ids tagged today; 12 more to tag). Charter: IN (the
   portable semantics). Decision: host capability — a machine-global
   matter the [USER] owns.
7. **Go version evolution (1.27 pin moves; spec drift tracking).**
   Known: both pins move together with a written reason
   (`spec-sources.md:15-19`); P0 probes showed 158 spec anchors
   identical 1.25.13 → 1.26.5, text churn 92/78; the version sweep
   script exists (one toolchain). Decomposition: a pin-move runbook
   (sweep → full `--diff` under the candidate → spec anchor diff →
   inventory re-audit U-7 → re-pin both) — S to write, M to run.
   Decision: when go1.27 ships — a [USER] call each time.
8. **The iris-lean customer integration itself.** Known: plan §1 is the
   interface; §1.14 the instantiation sketch; G-PIN's four conditions;
   the revival guide's owed items (σ-conditioned `wp_plug_bind`, G-REPR,
   the judge cadence). Decomposition here is DONE to the pin (§3.A); what
   is not decomposed is the OTHER side — the reasoning repo's creation
   (§3.I item 4) and its `Audit.lean`-class deletion test enforcing that
   no theorem's statement closure reaches a `GoCore` constant outside
   `Interface.lean`. Decision: the migration-stage decisions.
9. **Frontend correctness beyond translation validation (SpecTec-Go).**
   Known: §3.F item 4 — the route, the 249-row obligation census, the
   external tool; nothing else here. Decomposition would need: (a) the
   Go spectec document to exist (external, sequential Go first); (b) a
   certificate checker in Lean consuming the wire + the spectec AST; (c)
   the first three certificates (if-init hoisting, comma-ok,
   shadow-capture) as a pilot; (d) the K2 latitude rows stated as
   membership, never gc-equality. Charter: IN (frontend is trusted
   surface); the tool is not ours. Decision: when the tool exists,
   commission the pilot; until then, keep the census current (re-anchor
   owed).
10. **Interpreter performance as a coverage limiter (BUG-090 class,
    materialization budgets).** Known: A2's dense heap landed;
    re-measure OWED; `arrayLenBudget` 1<<16 (`operational-lessons.md:
    171`); noodler cliffs (recursion 20000 → 123 s; slice 10000 → >150 s);
    BUG-078's `normalizeListWith` linearity (`TODO.md:440-454`); the
    enumerator optimisation layers recorded not scheduled (`TODO.md:
    187-209`: POR, symmetry, preemption bound, memoisation, PCT).
    Decomposition: a measured re-baseline after A2 (S), then a budget
    ledger (which rows are capped by which budget) — the rows are known
    (`repeat-bound-refused`, `over-budget`, fuzz sizes). Charter: IN
    (coverage is the lower bound's reach). Decision: none — schedule the
    re-measure.
11. **Fuzzing at scale (grossmith).** Known: 39,800 judged, zero machine
    bugs; the infra failure class (ARG_MAX) fixed; the widening ladder
    and cadence PROPOSED. Decomposition: the ladder IS the
    decomposition; each rung is a generator config + a leg. Decision:
    the cadence (§3.E item 2).
12. **Independent review cadence.** Known: every lane has a pre-merge
    adversarial audit; the outsider legitimacy review happened once for
    the reasoning product (revival guide); this document exists for a
    whole-project review. PROPOSED [AGENT]: a whole-project review at
    each pin offer and at each oracle pin move, using §6.3; decision:
    the [USER]'s.
13. **Public release readiness.** Known: nothing is tracked about
    licensing of imported corpora (goose bodies, GOROOT test files under
    `Corpus/`, grossmith generator, cedar-go sources in `deps/`), about
    reproducibility from a clean clone (`scripts/setup-deps` needs
    `--from` a sibling checkout for `covmap`; the oracle is a host
    toolchain), or about docs for an external reader (`architecture.md`/
    `roadmap.md` are OWED rewrites). Decomposition would need: a license
    inventory of everything under `Corpus/` and `deps/` (S), a clean-clone
    CI run (the workflow exists; whether it passes from scratch is not
    recorded here), and the two rewrites. Charter: IN when the [USER]
    says so; today OUT (push itself is a per-event sign-off). Decision:
    whether and when.

---

## 5. Sequencing and the next wave

### 5.1 Dependency graph (text)

```
LANDED (main SHAs; §3 has the rest): A-series A1 8738d04d … A10 4c57a876,
        B1 fd3a3e9e, wave (iii) 1ebd7465/dfe763f9/50e3ea41, G-U e58eff5e,
        B4+C5 75d29186/1a82f305, C2 21bb79f7, stdlib slices 9acf0f43/e92285c0/6a73d02d,
        FR-19 249dc607, FR-27 6caf9c18, FR-4/22-25/28 partial (§3.B),
        strict-routing 82f74922, sampling-budget f98d4919, atomics w1 1b3796c6,
        detector-soundness 05d0ec54/5da5d8ff, gotest-fixes fa589f62
LANDED (round 17): e13-b 2fb7d54d → 7677865a (E13 (b); BUG-101/102/104; 12th site; twin pin 758110a3…)

A  B7 ──► C1 ──► P ──► C3 ──► I5 ──► assessment re-run ──► G-PIN offer
   B6 ──► C4 ──────────────────┘             ▲
   B5 (optional, any time; may follow the pin)│
   relational-module extraction ─────────────┘ (at/before migration)

C  narrowed slice 4 (strconv leaves) ─┐
   G6 T1 reflectlite (after C2: NOW) ─┼─► G6 T2 (after P) ─► G6-4 fmt (needs G7) ─► T3 ─► G6-5 json
   G7 os trio (BLOCKED: primitive cap) ┘

B  FR-1/2/3/6/7 (S, no deps) · FR-9 (raft) · FR-10 AFTER C1 · FR-13 WITH C2 (now) ·
   FR-11/20 goto → Signal modes (after B4: now) · FR-12 (M-L; cedar path) ·
   FR-31 (e13-b has landed — unblocked) · FR-26 · FR-15 LAST

D  e13-b LANDED ─► E12/E2 value-axis gate (BUG-101) ─► E2 two-point envelope (E12 rides it)
   E7 site · R3 arm · E3/E4 envelope · R7 · R18/FR-30 · BUG-080 (b) · atomics w2

E  step 5a for round 17 DONE (79214ab2) · cadence ruling · second toolchain · reconciler C15/mirror check
G  three-bug lane: BUG-103 (machine arm) · BUG-098/FR-31 · BUG-104 (all unblocked at 7677865a)
H  cedar first MATCH ⇐ FR-31 + T1 + slice 4 ⇐ then FR-12 for the authorization path
   raft W4 stage 2 ⇐ [USER] restart + FR-9 + E7
```

Cross-package couplings that bite if ignored: FR-10 before C1 bakes a
view into `Mem` twice; G6 T2 before P reads a D2 record whose meaning P
changes; FR-31 before e13-b would have conflicted in `emit.go` (moot since the rebase); C4 before B6 has no
`VarId` to allocate by; any wire-touching train without step 5a leaves
the certified set stale (C9 — exactly what happened between `7677865a`
and `79214ab2`, and was closed).

### 5.2 The recommended next wave ([AGENT] coordinator recommendation, as relayed in this lane's brief)

Four lanes in parallel, then one:

1. **B7** `ProgramCtx`/`Store` (+I1) — the critical-path hinge; 2
   sessions; no gate. Exit §3.A item 1.
2. **G6 T1 `reflectlite`** — RULED, unblocked by C2's landing; 2.5-4
   sessions (+1 for the `facility` class). Exit §3.C item 2.
3. **B6 `VarId`** — parallel, 2-3 sessions; twin pin moves — coordinate
   the fresh-emit rule with any other pin-moving lane in the same train.
4. **Three-bug fix lane** — BUG-103 (one machine arm; template
   BUG-020's rows), BUG-098/FR-31 (`methodWireName`, frontend-wide),
   BUG-104 (`safeExpr`-style decomposition). Exit: the 1 + 3 + 5 rows
   PASS; the BUG-098 guard retires; cedar `all` revives; a BUGS Cases
   line for any PASS→non-PASS. All three are unblocked at `7677865a`
   (e13-b has landed; the `emit.go` conflict is moot).

Then **C1** (G-C1) after B7 lands — 4-6 sessions, the trace-equality
audit, the detector re-run. C2's landing also lets FR-13 be designed
now; the narrowed slice 4 is an S-sized lane any time.

### 5.3 Calendar points

- **Assessment re-run** — after I5 (plan §5.2); expected "unchanged"
  and that is the claim; must add the `Accepted`/`run_refusal_free`
  frontier as a graded item. Estimated position: ≈ 17-22 sessions of
  critical path from B7.
- **Pin offer (G-PIN)** — after the re-run, under plan §5.3's four
  conditions; the migration-stage [USER] decisions (§3.I item 4) come
  due at the same time.
- **Step 5a** — done for round 17 (`79214ab2`); next due at the first
  train that touches `wire.go`/`NativeToIR.lean` (B6, P, FR-31 all will).
- **Decay reviews** — D-002 2026-10-31; D-001 2026-11-30.
- **Oracle pin move** — when go1.27 ships (a runbook is owed, §4 item 7).

### 5.4 Decisions the [USER] must make, and when

| when | decision | where posed |
|---|---|---|
| now | E2/E12 value-axis design gate (BUG-101): (a) envelope vs keep the red row | §3.D item 2; `docs/BUGS.md` BUG-101 |
| now | ratify the C6 §5.1-item-1 narrowing ([AGENT] 2026-09-05) | §3.B item 18; ledger 462-481 |
| now | primitive-cap re-ratification for G7 (`os.Exit`, `os.Stdout/Stderr`) — G6-4 depends on it | §3.C item 7; register 36, 95 |
| now | overlay-import cap 8 ([AGENT]-provisional) | register 34, 360 |
| now | G3 anchor widening beyond source-through packages (primitive rows cite file:line) | §3.C item 11; S3 174-180 |
| when posed | D-002 "not shim injection" reading of the atomics shadow model — `TODO.md:295-297` says confirmation owed while the register records it CONFIRMED 2026-09-03; one of the two records is stale | §3.I item 2 |
| now | periodic legs cadence (gotest / grossmith / sweep / 386 / P4) or "on demand" | §3.E item 2 |
| now | baseline-header narrative out of the header (adopt/decline) | §3.I item 1 |
| now | guarded-wrong-answer marker for the ratchet (adopt/decline) | §3.G |
| now | BUG-061 / L-011: is `callinit`-dependent init order latitude to envelope, or a permanent pin? | §3.G; BUGS.md 77-89 |
| now | restart raft W4 stage 2, or leave parked | §3.H |
| when posed | `nonterm=` under `engine=dedup` (OQ5) | `TODO.md:352-358` |
| when posed | second toolchain install for the version sweep (machine-global) | `oracle-legs.md:102-110` |
| at G-PIN | migration-stage decisions: repo name, dependency mechanism, history strategy, `raft-proof-campaign` disposition | split plan "Deferred" |
| at G-PIN | NPDRF proof investment (weakened proved form) | fidelity decision 1 |
| each | merge sign-offs (per train), push (per event), audit scope/waiver (per lane) | `CLAUDE.md` merge protocol |

---

## 6. Provenance and maintenance

### 6.1 How this document is amended

Dated addenda at the end of the affected section, never silent edits;
each addendum carries [USER]/[AGENT] provenance and, for status
changes, the commit or branch. A status word changes only with its
evidence pointer. Numbers are never updated without their derivation
line being re-run and the command re-stated. When a landing note and
this document disagree, the landing note wins and the disagreement is
an addendum here.

### 6.2 What supersedes what

- The C-arc's authoritative sequence is `docs/2026-09-04_reasoning-
  surface-plan.md` §5.1; §3.A above INDEXES it and updates its status
  column. A change to the sequence is made there first.
- The stdlib plan of record is the memo §5/§6 + the register; the
  reflect plan is the G6 memo §4.5/§6. §3.C indexes both.
- The frontier's queue is ledger §5; §3.B indexes it.
- The latitude census is code (`ChoiceSite`) mirrored by inventory §0;
  §3.D indexes the inventory.
- Rulings live where they were recorded (plan §5.4; qrow-rulings;
  decisions-2026-08-31; the design notes' §0s). This document quotes
  them as relayed and never becomes their home.
- This document supersedes nothing. It is the map; the territory is the
  tracked docs it points to.

### 6.3 Brief for the whole-project review agent

Read `CLAUDE.md`, `AGENTS.md`, this document; then, in a fresh worktree
off `main` with `scripts/setup-deps --from <sibling checkout>`:

1. **Re-derive the snapshot** (§0.2, §2.1): the awk tally; `cat
   baselines/go-oracle-pin`; `sha256sum baselines/pins/twin-chdriver.
   wire.json`; `git log -1 main`. Any difference = the tree moved;
   record the new tip and proceed against it.
2. **Run the gate** (`scripts/capped scripts/ci --diff`, TMPDIR inside
   the worktree). Read the `RESULT` line and every step; a fresh
   worktree fails closed on plain `ci` (the certified records need
   `--diff`). Confirm the tail says `git_dirty=false`.
3. **Run the checkers**: `scripts/check-bugs.sh` (expect `wrong-answer
   0/0`), `scripts/check-stdlib-register`, `scripts/check-frontend-pins`,
   `python3 tools/reconcile-records` (read every finding; a C9 finding
   means step 5a is owed at that tip).
4. **Test the exit criteria** E1-E13 (§1.7) one by one; for each "met",
   find the evidence yourself; for each "NOT met", confirm the owning
   item in §3 and its status word.
5. **Audit the status words**: for a sample of ≥10 LANDED items, `git
   show <sha>` and confirm the commit does what the row says; for every
   RULED item, open the record pointer and confirm a [USER] quote (as
   relayed) exists there; for every PROPOSED item, confirm no ruling is
   claimed anywhere.
6. **Probe the honesty-critical surfaces**: inventory §10's five rows
   (§3.D); the ratchet's blind spot (§2.6, §3.G) — look for open BUG
   entries with `Pinned-by: none` whose prose says "wrong"; the four
   stale-records findings (§2.2).
7. **Probe the trusted surface for hidden defaults**: `git grep -n
   'unsupported\|\.internal' GoLean/GoCore/StepFn.lean | wc -l` and
   read a sample — each must name its cause; check `NativeToIR.lean`'s
   decoder refuses on unknown node kinds (no absorbing arm).
8. **Read one design note end to end** (recommended:
   `docs/2026-09-05_c-arc-c2-design.md`) against its evidence dir and
   its commits; judge whether the [AGENT]/[USER] provenance is exact.
9. **Report** with the same discipline as this document: every claim
   with its command or `file:line`; every disagreement with this
   document as a numbered finding; no verification claims.

### 6.4 Landing record

- Written in worktree `.claude/worktrees/master-plan-0905`, branch
  `master-plan-0905`, off `main` @ `9343a310`, rebased onto `7677865a`
  (§0.2 addendum), 2026-09-05, [AGENT] author under the [USER]
  commission of §0.1.
- Records-only change set: this file; a pointer line in `CLAUDE.md`
  "Pointers". `docs/ARCHIVE.md` indexes archive/park branches only
  (27 lines; no live plans), so no entry was added there.
- Effect on the tree at `9343a310`: `python3 tools/reconcile-records`
  gained one MEDIUM (C6, 16 e13-b bug cross-references in this file);
  cleared at the rebase onto `7677865a` (3 findings, none this file's);
  2 findings (C13, C5) at `79214ab2` after the 5a landing.
- Gate: `scripts/capped scripts/ci --diff` — first run on the dirty
  tree (this file uncommitted): `RESULT: PASS`, cases=3528 pass=3283
  fail=245, baseline diff FULL 3528/3528 no regression, negative 394,
  eval tests 198 ok, twin pin unchanged (`git_dirty=true` noted by the
  gate — it certified the worktree state, not a commit). The clean-tip
  re-run is recorded in the addendum below once it completes.

**Addendum 2026-09-05 ([AGENT], lane `master-plan-0905`) — the clean-tip
gate.** `scripts/capped scripts/ci --diff` at the committed tip
`d797fb94` (this file + the `CLAUDE.md` pointer, tree otherwise
byte-identical to `9343a310`): `RESULT: PASS`; 24 steps ok, 0 FAIL;
`differential coverage summary: cases=3528 pass=3283 fail=245`;
baseline diff FULL 3528/3528 no regression; negative baseline diff no
regression (394); `check-frontend-pins: ok [twin-wire] — fresh emit =
pinned wire (a9a2e2b14d60…)`; `check-stdlib-register: ok`; eval tests
198 ok; reconciler 4 findings, 0 HIGH, report-only (C13, C5, C6 — this
file's e13-b refs — C9); no `git_dirty` note (clean tree). Log kept in
the lane's `.tmp/ci-diff-clean.log` (untracked; the tail is this
paragraph and the commit message).

**Addendum 2026-09-05 ([AGENT], lane `master-plan-0905`) — the gate at
the REBASED clean tip.** `scripts/capped scripts/ci --diff` at
`5414d41e` (this file re-derived at `7677865a`; tree otherwise
byte-identical to `main` @ `7677865a`): `RESULT: PASS`; 24 steps ok, 0
FAIL; `differential coverage summary: cases=3593 pass=3347 fail=246`;
baseline diff FULL 3593/3593 no regression; negative baseline diff no
regression (394); `check-frontend-pins: ok [twin-wire] — fresh emit =
pinned wire (758110a3f5a2…)`; `check-stdlib-register: ok`; eval tests
198 ok; reconciler 3 findings, 0 HIGH, report-only (C13, C5, C9 — none
this file's); no `git_dirty` note (clean tree). This tail supersedes the
`d797fb94` one above for the current tip.

# Phase 2 — adversarial re-examination of the KEEP verdicts (lanes A2, A3, B, C, D)

[AGENT] phase-2 verifier report, 2026-08-31, branch
`fidelity-assessment`. Objects: `docs/assessment/lane-a2-ledger-frontier.md`,
`lane-a3-shims-spectruth.md`, `lane-b-lower-bound.md`,
`lane-c-upper-bound.md`, `lane-d-apparatus.md`. Mandate: try to BREAK
every KEEP / KEEP-with-caption. A KEEP survives only on a fresh argument
that holds under the [USER] goal (lower bound = everything real Go does;
upper bound = everything the spec permits; superbly validated).

Verdict vocabulary: **KEEP-SURVIVES** / **KEEP-WEAKENED** (surviving
condition named) / **KEEP-BROKEN** (→ REOPEN/ESCALATE with the breaking
argument).

Probes run this session under this worktree, scratch in gitignored
`artifacts/p2probe/` (nothing tracked modified except this file). Two
sub-agents gathered primary-source evidence on the apparatus and the
observation channel; every fact they returned is cited to file:line
below and was spot-checked.

Sandbox note carried to the user, not worked around: 32-bit **execution**
is blocked in this environment (`GOARCH=386` binaries abort with exit
133 / SIGTRAP); 32-bit **compilation/type-checking** works. See C-8.

---

## 0. Counts

| source report | rows examined | SURVIVES | WEAKENED | BROKEN |
|---|---|---|---|---|
| A2 (ledger + frontier) | 12 census KEEPs (+1 adjacent) | 3 | 6 (+1) | 3 |
| A3 (shims + spec-truth) | 4 | 0 | 3 | 1 |
| B (lower bound) | 8 | 2 | 4 | 2 |
| C (upper bound) | 8 | 1 | 4 | 3 |
| D (apparatus) | 5 | 0 | 4 | 1 |
| **total** | **37 (+1)** | **6** | **21 (+1)** | **10** |

The ten BROKEN rows: A2-F6, A2-Q3, A2-L1, A3-S7, B2, B11, C
DEMONIC-STRONG grade, C-8 (R1), C-13 (permanent pins), D-2.

Three attacks I mounted and had to withdraw are recorded as refutations
(A3-D3 nontermination/collision; C fuel-under-dedup; B13 confluent
fuel-drop) — the code was more defensive than the reports claimed.

---

## 1. The four cross-cutting breaks

Before the row-by-row table, the four findings that move more than one
row, each with a concrete probe.

### 1.1 `unsafe` is NOT refused — its constant surface is silently modeled, and it is platform-pinned

Breaks **A2-F6**, breaks one row of **B2**, and adds a third leg to
A3-D2's constant-fold REOPEN. It also breaches doctrine register #6's
own re-opening condition as written.

Probe (`artifacts/p2probe/fe3/uz/main.go`), exported clean with NO
refusal by `go run ./tools/nativefrontend`:

```go
type S struct{ a bool; b int64; c bool }
func unsafeLayout() int {
    return int(unsafe.Sizeof(int(0)))*1000 + int(unsafe.Sizeof(S{}))*10 + int(unsafe.Offsetof(S{}.b))
}
```

The emitted wire body is a single folded literal:

```json
{"results":[{"expr":"int","type":{"int":"int","kind":"int"},"value":"8248"}],"stmt":"return"}
```

`8248` = Sizeof(int) 8 · 1000 + Sizeof(S) 24 · 10 + Offsetof(S.b) 8 —
all three **implementation-specific** by spec#Size_and_alignment_guarantees
(only the fixed-width types' sizes are forced). gc on amd64 agrees
(probe: `gc amd64 run: 8248`). Computed with the *pinned toolchain's own*
`types.SizesFor("gc", …)`: 386 → `4164`, arm → `4164`.

Consequences:

- `docs/language-coverage-ledger.md:266` classifies `Package_unsafe`
  out-of-language because "modeling its observables = modeling gc's
  layout (the doctrine's anti-goal)", and says the boundary is "kept
  VISIBLE" by marker reds. The boundary is **not** a mechanism: the
  frontend refuses only the `unsafe.Pointer` wire TYPE
  (`unsafe/boundary/pointer-roundtrip`, "basic type unsafe.Pointer").
  Sizeof/Alignof/Offsetof over arbitrary types pass through
  `go/constant` at emit time and become wire literals. What keeps the
  corpus honest is *curation*: the case file
  (`Corpus/coverage/exec/unsafe/boundary/main.go:15-22`) deliberately
  uses only `int64`/`int32`, whose sizes ARE spec-forced — the case file
  is scrupulous, the mechanism is absent.
- Doctrine register #6 (`docs/2026-08-11_essence-of-go-doctrine.md:143-156`)
  makes the allocator-quotient discharge conditional on the observation
  surface, naming "`%p`, pointer order, `unsafe`" as re-opening
  channels. Part of `unsafe` is already in the modeled channel.
- Lane B's B2 table row "`uintptr` … `unsafe` is refused" and B6's
  endianness argument ("the only byte-order surface is the
  binary.LittleEndian shim, … and `unsafe` is refused") both rest on a
  refusal that does not exist for this surface.

Fix shape (S): a frontend refusal on `unsafe.*` selectors whose folded
value is not spec-forced, or — better and cheaper — refuse the
`unsafe` import outright and keep the two marker rows as
red-by-design; then the ledger row becomes true.

### 1.2 A 32-bit oracle exists and this project has already used it

Breaks **C-8 (R1 int width KEEP)**; falsifies B6's routing ("worthless
until a 32-bit oracle lane exists") and B8's uniqueness claim #3 ("the
R1 32-bit width point — unlocked by a tinygo/gccgo-386 leg and by
nothing else").

The fresh argument C-8 offers is "no 32-bit oracle exists, XIMPL is the
gating evidence class — unchanged and still true". It is not true:

- The **pinned toolchain itself** is a 32-bit oracle. `GOARCH=386` is
  the same gc at the same version — no second implementation, no
  install, no pin move. Probe: `GOARCH=386 go run` rejects
  `var x int = 1 << 40` with *"cannot use 1 << 40 … as int value
  (overflows)"* while amd64 accepts it. That is a width-dependent
  **static-semantics** discrimination available with zero
  infrastructure, and it directly bears on the delegation claim (A2-L1)
  and the negative lane, both of which are silently 64-bit.
- The project **already ran** a dynamic 386 leg:
  `docs/2026-08-20_grossmith-findings-2.md` §6 — 4,000 cases at
  `GOARCH=386` against gc-amd64, `match 3130 | observation-mismatch
  870`, "divergences in-tag 870, off-tag 0". Observation mismatches
  require execution. B6 cites this same number and still routes the row
  to B8.
- `GoLean/GoCore/Value.lean:32-43` hard-codes `int`/`uint` to 64 with
  **no caveat anywhere in the file** (grep for `platform` / `32-bit` /
  `GOARCH` / `width`: nothing but constructor names). The C-8 KEEP and
  the 20-days-owed caveat are the same debt.
- §1.1 shows the width pin already leaks into wire literals via the
  unsafe fold, unrecorded.

Honest scope: in THIS sandbox a 386 binary aborts (exit 133), so the
dynamic leg cannot be re-run here. That is an environment limitation to
hand to the user — per the sandbox rule I did not try to work around it
— not a defence of the KEEP. The compile-time leg needs nothing.

Recommended disposition: REOPEN (S) — a `GOARCH=386` compile leg over
the negative corpus and the width-tagged exec fixtures, recorded as a
realization-drift census; ESCALATE only the question of whether the
model should carry a width PARAMETER (that stays L).

### 1.3 Boundary claims that outran the boundary — three independent instances, all found by audit, none by a gate

A pattern that damages **A3-S7**, **A2-F7**, **A3-D3** and **B2**
simultaneously: the repo repeatedly documents a refusal that the code
does not deliver, and the discovery mechanism is always an adversarial
audit.

1. **New (this session), A3-S7.** The stdlib policy states the function
   VALUE shape "keeps existing refusals" (`stdlibshim.go:29-31`).
   Probe: `func funcVal() int { f := strings.Fields; return len(f("a b c")) }`
   exports with `funcVal` quarantined — fail-closed, correct — but the
   recorded reason is
   **`"field selector on anonymous struct type invalid type"`**
   (one of `emit.go:{4821,5191,5499}`; the `%s` argument printed as
   `invalid type`). There is no anonymous struct in the program. The
   charter's requirement is "an explicit refusal that NAMES ITS CAUSE at
   the point of failure"; this names a phantom cause. A3-S7's claim
   (iv) "narrowings named in refusals" fails on the exact row it cites.
2. **Recorded, mono.go:876-890.** The `renderTypeArg` refusal comment
   "used to also claim 'none of them can reach a supported wire type
   either' — true when written (pre-channels), FALSE since the channels
   arc made chan a first-class wire type". An unrelated arc silently
   invalidated a trusted component's refusal rationale; caught by
   arc-final audit F9.
3. **Recorded, BUG-068.** "the 2026-08-22 audit fix round … found this
   entry's first version claiming refusals the scan did not deliver;
   type-switch guards were SILENTLY MISSED … and aliased exactly as this
   bug describes" (`docs/BUGS.md:3275-3288`) — i.e. a *silent wrong
   answer* behind a claimed refusal.

Add A2-N1's negative-lane header ("+ frontend fail-closed" naming a
stage that does not exist) and §1.1's unsafe row and the count is five.
No gate in the repo compares a claimed boundary against a realized one.
This is the strongest systemic finding of my pass: it means **any**
KEEP whose fresh argument is "the boundary is fail-closed" carries an
untested premise, and the evidence class that has ever caught it is
adversarial reading.

### 1.4 The circular delegation of the race-detector completeness question

Breaks **A2-Q3**. The DRF-SC KEEP's fresh argument is "the refusal
direction is verified fail-closed; the completeness question explicitly
handed to lanes C/D". Following the hand-off:

- A2-Q3: "its soundness leg (detector completeness for accepted
  programs) is lane-C/D territory".
- Lane C §1c.3: "That soundness question is **Lane A's #4**; it is a
  CONDITION here." — handed straight back.
- Lane D: never audits it (its scope is the apparatus as an object);
  grep of `lane-d-apparatus.md` for detector/completeness: nothing.

So the one condition under which register #4 ("SC-only interleaving
within DRF", doctrine :127-133) is sound is owned by nobody, and each
lane's KEEP is licensed by the other's. This is the same shape as
A2-Q1's orphaned routing, but *inside phase 1's own output*. A false
negative in the detector would turn "SC-only" from an argued bound into
an invented behavior (C's own words) — i.e. a modeled ⊄ permitted break
at the largest concurrency row. REOPEN with a named owner; the substance
of the refusal direction is unaffected and stays KEEP.

---

## 2. Lane A2 — 12 census KEEPs (+1 adjacent)

| row | verdict | one-line reason |
|---|---|---|
| A2-F3 complex-last (FR-15) | KEEP-WEAKENED | prevalence is a *lower-bound* argument defending an *upper-bound* gap |
| A2-F4 small FRs 1–7, 9–13 queued | KEEP-WEAKENED | "queued" is the entire fresh argument, and the queue is provably non-consuming |
| A2-F5 C6 impossibility | KEEP-WEAKENED | impossibility is about the message/name PIN, not about the language |
| A2-F6 unsafe/print/println out-of-language | **KEEP-BROKEN** | unsafe's constant surface is silently modeled and platform-pinned (§1.1) |
| A2-F7 BUG-068 red-by-design rows | KEEP-SURVIVES | genuine fail-closed residue; caption: this entry is instance 3 of §1.3 |
| A2-Q3 DRF-SC + racy refusal | **KEEP-BROKEN** | circular delegation, the condition is unowned (§1.4) |
| A2-B6 the 61 fixed entries | KEEP-SURVIVES | strengthened: `check-bugs.sh` enforces polarity, not just presence |
| A2-L1 grade-D delegation as a class | **KEEP-BROKEN** | "structurally impossible" is false: two different type checkers |
| A2-L2 S3 D-caveat | KEEP-WEAKENED | same object A3-P3 REOPENs (M); a KEEP here understates it |
| A2-L5 T-3 blocked on A2-Q2 | KEEP-WEAKENED | correctly blocked, but a block with no owner reads as an orphan |
| A2-U1 untriaged ratchet | KEEP-WEAKENED | re-verified live; ceilings raise silently and clean deletion is unguarded |
| §2.3 `floats/to-int-out-of-range/{nan,range}` (R6) | KEEP-SURVIVES | spec implementation-dependent; refusal is the honest member |
| *adjacent:* §2.3 `same-name-identity-panic` (c)-pin C3 "impossibility argued" | KEEP-WEAKENED | impossibility is FRONTEND-scoped; the core fix is known and orphaned |

### A2-F6 — KEEP-BROKEN → REOPEN (S)

See §1.1. The `print`/`println` half survives independently (spec
§Bootstrapping: "not guaranteed to stay in the language … do not return
a result"); the body-less-function half survives (assembly linkage is
genuinely unrepresentable). The `unsafe` half does not: the spec has a
whole §Package_unsafe, so "the spec itself scopes these out" is wrong as
stated — the honest label is *refused latitude* (implementation-specific
sizes/alignment), the same class as R6 — and the boundary is enforced by
corpus curation rather than by the frontend. A2's own "S nit" about the
`marker reds` plural is the visible tip of this; the substance is that
`unsafe.Offsetof` values reached the wire.

### A2-Q3 — KEEP-BROKEN → REOPEN (ownership)

See §1.4.

### A2-L1 — KEEP-BROKEN → REOPEN (S, restatement)

The fresh argument is: "both the oracle and the machine consume the same
go/parser+go/types-checked program, so for ACCEPTED programs a
static-semantics divergence between the two sides is structurally
impossible. This is the strong, honest core."

They do not consume the same checked program.

- Our frontend type-checks with the **standard library `go/types`**:
  `tools/nativefrontend/load.go:31-40` imports `go/types`,
  `load.go:641-649` runs `conf.Check(...)` and refuses on error; the
  stdlib half of the importer is `importer.Default()` (`load.go:95`),
  i.e. gc **export data**. Grep for `types2` across
  `tools/nativefrontend/`: **zero hits**.
- The oracle `go run` type-checks with `cmd/compile/internal/types2` — a
  sibling fork of go/types, kept in sync by hand, not proven equivalent.

So the impossibility is not structural; it is an *assumed equivalence of
two implementations*. And the assumption is already known to fail on
derived output that reaches dynamic observables: `go/types`' `InitOrder`
vs gc's initorder is exactly deviation E7 (`emit.go:1281-1316`
consumes `u.info.InitOrder`; C §3 records the divergence; the row is a
standing differential red). The negative lane compounds it: it exercises
PATH `go build` (types2) while the frontend's refusals come from
go/types, with nothing detecting skew (A2-N2).

Restatement to adopt: *GoLean models the dynamic semantics of programs
that `go/types` at go1.26.5 accepts; agreement between `go/types` and
gc's `types2` on the accepted set is an untested assumption, and the
inter-package init schedule is separately pinned to gc's realization
(`load.go:15-29`: "The schedule is gc's, not the spec's literal
reading").* The §1.2 386 probe shows the acceptance set is also
silently width-conditioned.

### A2-F3 — KEEP-WEAKENED

Surviving condition: FR-15's queue position may be defended by
prevalence, but the *gap* may not. Complex is 19% of refusals and a
spec-mandated type class; under the upper-bound claim (permitted ⊆
modeled) prevalence is not an argument at all — it is a lower-bound
argument. Two couplings the KEEP does not price: A2-L2 records that
FR-15 is "the first large GoCore-arithmetic surface where delegation
stops covering for us", so deferring it also defers *discovery* of the
delegation hole; and complex constants ride the same go/constant fold
(A3-D2) that §1.1 shows is already carrying implementation-specific
values.

### A2-F4 — KEEP-WEAKENED

The fresh argument for each of FR-1/3/4/5/6/7/9/10/11/12/13 and
mini-slice A3 is "queued"; A2 itself measures **zero of 14 queue slots
consumed via the queue in 12 days** and files a REOPEN on the
scheduling. A per-row KEEP whose content is a position in a stalled
queue is re-dressing. Surviving condition: an owner and a date, or the
rows are relabelled backlog. Sub-note under the new goal: FR-12
(range-over-func) is the mechanism behind `iter.Seq` and the Go 1.23+
`slices`/`maps` iterator idiom — its queue position (#12) encodes 2026's
raft plan, not "everything real Go code does"; it should be re-ranked in
the same sitting as A2-F1/F2.

### A2-F5 — KEEP-WEAKENED

The argument ("gc's observable name embeds a compiler-internal counter;
no injective spec-derived name exists; refusing is the only honest
member") is correct about *reproducing gc's spelling* and wrong about
*the language*: the spec fixes no name for a function-local defined
type, so any name conforms and refusal is strictly NARROWER than
permitted. What makes reproduction necessary is our own equality lane —
the compared first-panic line pins gc's strings (R9). The project
already owns the technique that dissolves this: the **R-1 ruling**
(`docs/2026-08-20_w32-re-envelope-charter.md:335-394`) quotients the
TEXT and keeps the forced half exact, executed on four rendering rows.
Surviving condition: keep the refusal as the honest interim, but record
that the blocker is the message pin (an R-1-class quotient), not an
impossibility — otherwise the row inherits a permanent exemption it has
not earned. Same correction applies to the adjacent
`same-name-identity-panic` (c)-pin: `docs/2026-08-18_multipackage-identity.md:131-138`
says it is "NOT fixable **frontend-side**" and names the structural fix
(display/identity split in the core), filed as **BUG-059** — which is one
of the four orphaned bugs A2-B4 escalates. "Impossibility argued" in
A2 §2.3 over-reads its own source; the row belongs with A2-B4.

Probe supporting both: gc renders instantiated/qualified names by
package NAME (`interface conversion: inner.T is not interface { Foo() }`
for a type at path `red/inner`), while our TypeId is path-qualified
(`emit.go:4651-4663`) — one string doing double duty as identity key and
display name.

### A2-F7 — KEEP-SURVIVES

The two red-by-design rows (`range-clause`, `ts-guard`) are genuine
fail-closed residue of a real fix and are excluded from the fixed-case
list on purpose (`docs/BUGS.md:3296-3299`). Caption owed: this entry's
first version claimed refusals that did not exist and type-switch guards
were silently aliased — instance 3 of §1.3.

### A2-B6 — KEEP-SURVIVES (strengthened)

The "mechanical Cases check is the argument" claim is stronger than
stated: `scripts/check-bugs.sh:74-83` checks **polarity**, not presence
— `fixed/FAIL` and `open/PASS` both FAIL the gate, and a missing id
FAILs. Latent nit: the `case` has no default arm, so a baseline result
token outside `{PASS,FAIL}` would fall through silently (today the
vocabulary is exactly those two; 2306/172).

### A2-L2, A2-L5 — KEEP-WEAKENED

L2: the caveat is honest, but it labels a measured evidence hole that
lane A3 files as **REOPEN (M)** (A3-P3, runtime twins of the literal
grids). One object cannot be a KEEP in one lane and a REOPEN in another;
adopt A3-P3's disposition and keep the caveat as its caption.
L5: correctly blocked on A2-Q2 — but A2-Q2 is itself a REOPEN with no
owner, so the KEEP rests on a REOPEN foundation. Surviving condition:
the block carries A2-Q2's owner and date, or it is an orphan.

### A2-U1 — KEEP-WEAKENED

Re-verified live this session: `baselines/untriaged-count` = `coverage
11 / latitude 4 / wrong-answer 0`; `baselines/untriaged-ids` = 15 data
rows (11+4), i.e. **both live classes are AT their ceiling**. The
ratchet is real. Three conditions the KEEP does not name:

- Ceilings can be **raised silently**: `check-bugs.sh:234` compares only
  `-gt`; the ratchet-down advisory (`:278-281`) prints only on an
  otherwise-green run and never fails; nothing compares
  `untriaged-count` against its own history. `coverage 11 → 50` passes
  every gate.
- A failing corpus case deleted **cleanly** (cases.tsv row + baseline
  row + its `untriaged-ids` row and/or BUGS `Cases:` citation) passes
  every gate: the re-pin flip guard computes `oldpass \ nowpass`
  (`ci:661-667`) so a FAIL id was never in the domain;
  `coverage-baseline-diff --full` iterates the *new* baseline
  (`:60-63`); `ci:541` derives `total` from the current corpus. There is
  **no corpus-size ratchet anywhere in `scripts/`**.
- The "0 wrong-answer" floor counts UNTRIAGED wrong answers. Five known
  wrong answers (BUG-062) sit outside it by explanation — as
  grossmith-findings-2 §7.1 already says in its own words.

---

## 3. Lane A3 — 4 KEEP rows

| row | verdict | one-line reason |
|---|---|---|
| A3-S5 per-shim deltas (7 sub-rows) | KEEP-WEAKENED | deltas hold; one sub-row's failure mode does not name its cause |
| A3-S7 fail-closed on out-of-set stdlib | **KEEP-BROKEN** | the value-position refusal names a phantom cause (§1.3) |
| A3-Q3 the three W3.2 parks | KEEP-WEAKENED (1 sub-row BROKEN) | one park's condition has fired; one item's observable does not exist |
| A3-D3 monomorphization | KEEP-WEAKENED | substance survives two attacks; the headline over-claims and the fence is queued to be dismantled |

### A3-S7 — KEEP-BROKEN → REOPEN (S)

See §1.3.1. Two of the four boundaries re-verified as genuinely good and
worth recording, because they refute weaker attacks I tried:

- **Aliased imports work correctly.** `import s "strings"; s.Fields(x)`
  injects the shim (probe `artifacts/p2probe/fe/alias`) — the injection
  scan is types-based, not identifier-text-based.
- **Shim calls inside generic bodies and in `defer` closures work**
  (probes `fe2/generic`, `fe/deferred`): the stencil
  `countIn[int]` and the deferred call both carry the injected
  `goleanShimStringsFields`.
- **Dot-import reproduces the known S4 defect**: no shim injected, a
  dangling plain call, machine `stuck` (probe `fe/dotimp` — the wire
  contains no `goleanShimUnsupported` decl at all).

So the break is narrow and precise: the boundary is *drawn* correctly
and *reported* wrongly on the value-position row. Under the charter that
is a defect ("NAMES ITS CAUSE at the point of failure"), and it is the
kind an outside reviewer finds in one probe.

### A3-S5 — KEEP-WEAKENED

Re-checked at source. `strings.Repeat`'s negative-count panic IS
verbatim upstream (`stdlibshim.go:1163-1166`:
`panic("strings: negative Repeat count")`) and, per the header
(`:120-132`), upstream-faithful panics deliberately stay ordinary
recoverable panics while golean refusals route through the
unrecoverable `goleanShimUnsupported` throw — that split is right and
the KEEP is right about it. The two conditional-unobservability
tripwires A3 already owes stand.

The one sub-row that weakens: the Repeat output-length-overflow delta is
argued as "a visible stop, never a wrong answer" — but the stop is
*fuel-out or memory exhaustion*, the only delta in the table whose
failure mode does **not** name its cause, and a memory blow-up under
`scripts/capped` presents as infra death rather than a refusal. Low
stakes (the overflow needs astronomically large counts), cheap fix (a
modeled bound check that refuses by name). Surviving condition: the two
tripwires plus one cause-naming refusal here.

### A3-Q3 — KEEP-WEAKENED, one sub-row BROKEN

- **Trace-coverage push — BROKEN.** The park's [USER] condition is
  "post-campaign". The campaign pivoted (2026-08-27/28) and the repo
  split (2026-08-31); the condition has **fired**. A park whose
  condition is satisfied is not a park — it is an unowned item wearing
  [USER] provenance. A3 itself notes the condition "is now ambiguous
  and should be re-stamped"; under the mandate that is a REOPEN (S,
  a re-stamp), not a KEEP.
- **Slice-5 print-interleaving probe — WEAKENED to the point of
  vacuity.** Its observable is interleaved *print* output, and lane B's
  own B1 establishes that **program stdout is not in the observation
  channel at all** (and `fmt.Println` quarantines the declaration).
  The item cannot be probed through the differential without widening
  the channel — which would re-open register #6/C11 (B3). Surviving
  condition: re-state it as a channel-widening design question with
  B3's tripwire attached, or retire it.
- **Map-range pick-walk cost — SURVIVES** (the TODO itself rules
  semantics not in question; perf only).

### A3-D3 — KEEP-WEAKENED (headline over-claims; fence is queued for demolition)

**Two attacks mounted and REFUTED — recorded because they are the
obvious ones and the code wins:**

1. *Termination of full stenciling.* Full monomorphization does not
   terminate on polymorphic recursion, and I expected the frontend to
   inherit totality from go/types' "instantiation cycle" implementation
   restriction (i.e. from a delegated `may`-restriction, which would be
   a permitted-⊄-modeled hole with no local guard). Wrong: `mono.go:819`
   caps the instantiation registry and refuses by name —
   `"instantiation registry exceeded %d distinct mangled keys
   (monomorphization cap, design note §2e)"`. Total by its own
   construction, fail-closed.
2. *Mangled-key injectivity across packages.* `mono.go:807-818`
   refuses on a real collision (`"mangled TypeId collision: %q names
   both %s and %s"`) and admits only `types.Identical` re-registrations;
   the qualifier space is covered by `checkKeyPathGrammar`
   (`identity.go:128-144`) plus path-qualified names
   (`emit.go:4651-4663`, the BUG-010 fix).

**What lands.** The KEEP's headline — *"the spec defines generic
semantics by INSTANTIATION … so full monomorphization is a faithful
realization of the spec's own definition"* — is a category claim that
does not do the work. The spec's instantiation rule is a typing/semantic
definition, not a mandate on realization strategy; "no spec sentence
makes implementation strategy observable" is the real claim, and it is
true only **relative to the admitted surface**. That surface is held by
four refusal fences, and the KEEP names only two of them:

- function-local defined types as type args (`mono.go:903-910`);
- anonymous non-empty structs/interfaces as type args
  (`renderTypeArg`, `mono.go:871-890`);
- unnamed channel types as type args (same site — and note this arm's
  own rationale was silently falsified by the channels arc, §1.3.2);
- `reflect` and `%T` unmodeled (the fmt verb/kind matrix).

Two of these are **queued frontier rows scheduled to land** (FR-13
anonymous non-empty struct TypeIds, "M (small arc)", A2 §0.2 group 6;
and the fmt/reflect surface widens with FR-14/the shim boundary). Live
probe of what happens when the anon-struct fence comes down:

```
reflect Name:              "Pair[struct { X int },int]"
panic text (gc, verbatim): interface conversion: interface {} is main.Pair[struct { X int },int], not main.Inner
types.TypeString:          "struct{X int}"
```

`types.TypeString` — the natural implementation — spells the type
argument **without spaces**; gc/reflect spells it **with**. Panic text
is IN the compared channel. mono.go already special-cases exactly this
for the *empty* forms ("`interface {}` for the empty interface,
`struct {}` for the empty struct", file comment :17-20) — i.e. the
divergence class is known and handled only where it is currently
reachable. Landing FR-13 without re-deriving the spelling rules
converts a fail-closed refusal into a silent panic-text divergence.

Surviving condition (the whole KEEP): a recorded tripwire binding the
`renderTypeArg` mangling surface to the frontier queue — FR-13 and any
reflect/`%T` widening must re-derive mono's identity contract before
landing. The precedent (§1.3.2) is that without such a tripwire this
exact thing happens and an audit finds it later. A3's named residual
(1,063 + 9,103 lines of trusted lowering with no translation validation)
stands unchanged.

---

## 4. Lane B — 8 KEEP rows

| row | verdict | one-line reason |
|---|---|---|
| B1 channel map | KEEP-WEAKENED | three corrections; the map overstates what non-ok rows compare |
| B2 out-of-channel observables fail-closed | **KEEP-BROKEN** | the `unsafe` row of the table is false (§1.1) |
| B5 version-pin mechanics (KEEP-flavoured) | KEEP-WEAKENED | absent `go` ⇒ note ⇒ PASS; negative lane has no pin check |
| B7 `-race` discipline | KEEP-SURVIVES | genuinely a second oracle MODE, correctly never mixed with deadlock rows |
| B9 corpus as anchored regression suite | KEEP-SURVIVES | routing to B10 is right; add the integer-only-args caption |
| B11 negative corpus wording | **KEEP-BROKEN** | the kept sentence IS the overstatement A2-N1 flags |
| B12 certification modes | KEEP-WEAKENED | the flip guard is one-directional; deletion unguarded; `tier=slow` = 1 row |
| B13 ∀-stream lanes | KEEP-WEAKENED | cardinality is pinned on 15 of 25 membership rows |

### B2 — KEEP-BROKEN (one row) → REOPEN (S)

See §1.1. Every other row of the B2 table re-verified as described. The
break matters beyond bookkeeping because B2 is the mechanism B3's
forward-risk analysis and B6's endianness argument both lean on.

### B11 — KEEP-BROKEN → fold into A2-N1 (REOPEN S)

B11 keeps the wording *"gc's frontend rejects these and **our pipeline
agrees they're outside the domain**"*. The second clause is precisely
the stage A2-N1 shows does not exist: `scripts/coverage-negative:101-111`
runs one `go build` per case and no GoLean tool has ever seen the 390
programs. Confirmed additionally this session: `coverage-negative` has
**no oracle-pin check at all** (grep for `go-oracle-pin`: not found), so
a standalone run against a drifted toolchain records silently. A KEEP
that re-states the flagged sentence and defers the wording is not a
fresh argument.

### B1 — KEEP-WEAKENED (three corrections)

1. **Interface boxes carry the package-UNQUALIFIED name.** `CLI.lean:78-93`
   ("renders type names the way Go's `reflect.Type.Name()` does —
   WITHOUT the leading package qualifier") via `TypeId.unqualified`
   (`Value.lean:261-269`). So the `typeName` field cannot distinguish
   `red/inner.T` from `blue/inner.T`. No hole in practice — cross-package
   identity is witnessed *behaviourally* by
   `multipkg/same-name-identity` (a green ok row whose result encodes
   five assert outcomes) — but the map's wording ("dynamic type NAME")
   overstates that field's discriminating power, and the one place the
   qualified name IS observable (panic text) is the ratified C3
   divergence.
2. **For every non-ok row the value payload does not participate.**
   `scripts/diff-coverage:498/510/535/549` *replaces* the Go observation
   with a synthesized `{status, message}` object; 191 of 2478 rows are
   non-ok, and the 21 racy + 19 deadlock rows compare a **constant
   string** (`"data race detected"` / `"all goroutines are asleep -
   deadlock!"`) with no case-specific content. Separately, only 23 rows
   have a zero-result subject, and `tools/coverageharness/main.go:318-321`
   refuses a zero-result subject for `expected_status=ok` — a good
   fail-closed guard worth naming in the map.
3. **Subject arguments are integer-only** (`main.go:32`, `parseArgs`
   `:218-252`, explicitly "deliberately NOT a per-parameter type
   check"). Argument-driven variation across the corpus is confined to
   integers; every other input shape must be built inside the subject.

### B5 (pin mechanics) — KEEP-WEAKENED

The three-layer pin is real and the incident history behind it is
exemplary. Two fail-open edges the KEEP does not name:

- `scripts/ci:179`: **`go` absent on PATH ⇒ a `note`, and `RESULT: PASS`.**
  `RESULTS+=` does not set `fail=1` (only `bad()` does, `ci:96`). The
  charter's own words: "a gate that cannot run FAILS rather than skips."
  This is the *only* missing-tool→note site in `scripts/` — every other
  tool-absence path FAILs (`check-imported-goose:41`,
  `check-spec-anchors:42-46`, `check-frontend-pins:39-40`) — so it is an
  outlier, not a house style, and the fix is one line.
- `scripts/coverage-negative` has **no pin check**; the negative lane is
  pinned only transitively when invoked under `ci` (whose step 0c ran
  first), and it also reads `GO_TIMEOUT_SECONDS` without the
  fail-closed validation `diff-coverage:72-75` applies.

### B12 — KEEP-WEAKENED

The publication-integrity machinery re-verifies as described and is
genuinely the strongest-audited part. Three additions that change the
grade from "strongest-audited" to "strongest-audited, with named
fail-opens at the edges":

- **Non-PASS → PASS is unguarded.** `ci:661-667` computes `oldpass \
  nowpass` only. A baseline row edited `FAIL → PASS` produces no flip
  and owes no BUGS.md `Cases:` line. Its only backstop is a live run —
  which push/PR CI does not perform (`GOLEAN_ALLOW_NO_DIFF=1`, §5.2).
- **Clean deletion of a failing case is unguarded** (A2-U1 above; no
  corpus-size ratchet).
- **`tier=slow` is exactly ONE row** (`imported-goose/channel/google-search`;
  every other slow-tier row was moved to `engine=dedup` by the
  2026-08-21 POR slice). So `--slow` differs from `--diff` on one row,
  and the nightly's headline strength rests on that row.

### B13 — KEEP-WEAKENED

**Attack refuted, recorded:** I expected a confluent `|set|=1` row to be
able to drop fuel-cut branches silently under `--allow-nonterm`. It
cannot: `nonterm=` is manifest-restricted to the membership lane
(`coverage-manifest:381-383`, mirrored `diff-coverage:983-997`), the
confluent enumerator argv never passes `--allow-nonterm`
(`diff-coverage:614-622`), and without the flag a fuel-cut branch is a
hard `.error` (`CLI.lean:1271-1274, 1282-1285`) that fails the whole
case. **Zero rows carry both `nonterm=` and `engine=dedup`**, and the
combination is refused fail-closed (`CLI.lean:1485-1487`).

What weakens the KEEP:

- "set CARDINALITY pinned (`members=n`)" holds on **15 of 25**
  membership rows. Ten carry no `members=`; two of those state a
  cardinality in prose only (`mini-raft-twin` "admitted set {21,31}
  (members=2)", `maps/jitter-draw` "{5,6,7,8,9} (members=5)"), and the
  pin at `diff-coverage:1206` is skipped when the param is absent — so
  those sets may grow or shrink without failing.
- The one live `nonterm=` row (`goroutines/send-then-spin`,
  `members=1,nonterm=200`) **disables the singleton guard**
  (`diff-coverage:1195-1198`) and suppresses coupling-stream checks that
  land fuel-out (`:1224-1231`); its header records `nonterm=216` pruned
  branches that no gate re-checks. That is a live instance of A3-Q2's
  OQ5 ambiguity, not a hypothetical.

---

## 5. Lane C — 8 KEEP rows

| row | verdict | one-line reason |
|---|---|---|
| C-2 reg-gran: KEEP the honest labeling | KEEP-WEAKENED | the honesty is local to NPDRF.lean; the citing register does not carry it |
| C-3 modeled ⊆ permitted (KEEP + REOPEN S) | KEEP-WEAKENED | the "declared canonical default" leg is a docstring String derived from the code |
| C DEMONIC-rows-STRONG grading | **KEEP-BROKEN** | ≥3 of the 9 DEMONIC rows are recorded non-maximal at their own sites |
| C-6 fuel claim-level ruling | KEEP-WEAKENED | main attack refuted; `--allow-nonterm` conflates slow with divergent and is unrecorded on green |
| C-8 R1 int width | **KEEP-BROKEN** | "no 32-bit oracle exists" is false (§1.2) |
| C-12 `Fair` as recorded-owed | KEEP-SURVIVES | domain defined, predicate absent, consumer note owed — accurate |
| C-13 the nine permanent-pin candidates | **KEEP-BROKEN** | refuted by the project's own R-1 text-quotient ruling |
| C-7 register #7 KEEP-recommendation (a) | KEEP-WEAKENED | acceptable only with the domain-condition rider made mandatory |

### C DEMONIC-STRONG — KEEP-BROKEN → downgrade the grade

C's closing grade says "The DEMONIC rows themselves are STRONG at their
stated granularity." C's own table and the code say otherwise for at
least three of the nine:

- **R2 (append spill).** `Ops.lean:1940-1943`, verbatim: spec §Appending
  means "ANY capacity ≥ newLen is conforming, **so the envelope is a
  pragmatic SUBSET of that latitude**". Worse for the grade: the upper
  bound `max 32 (2 * growth)` is justified by **probes against
  go1.26.5** (`:1944-1962`, the 32-byte stack buffer and size-class
  rounding) — i.e. a DEMONIC row whose width is calibrated to the
  oracle's realization, not to the spec.
- **E9 (map iteration).** `Machine.lean:1764-1770`, verbatim: "Residual
  narrowing, recorded: … a DRF cross-goroutine delete … does not prune
  other goroutines' in-flight produced/start sets — re-production of a
  cross-goroutine deleted-then-re-created key **is not realized**." An
  acknowledged under-approximation of the envelope, with a re-envelope
  obligation open at inventory E9.
- **C3 (post-op interleave).** C's own table: "B3 abort window DEFERRED
  … — a residual PIN", and C-10 files the trigger as wired to nothing.

Add that C5's containment (U-2, L4 ⊆ L1-reach) is `[ANALYSIS]` with no
theorem, and C2's grain is the very residual the reg-gran row disputes.
The defensible grade is: **STRONG for the spec-silent scheduling rows
C1/C4/C8 at registry granularity; ADEQUATE-with-recorded-narrowing for
C2/C3/C5/E9; and R2 is a declared subset, i.e. an intentional
permitted-⊄-modeled row that should not be counted DEMONIC-STRONG at
all.** This matters because the DEMONIC count is the one place the C3
grade is currently allowed to be strong.

### C-8 (R1) — KEEP-BROKEN → REOPEN (S) + the owed caveat

See §1.2.

### C-13 (permanent-pin candidates C9/E8/E10/E11/R5/R8/R9/R11/R12) — KEEP-BROKEN → REOPEN

C's read is "all nine survive as version-tracked pins with transfer
caveats (their observables are message/exit/text-identity classes where
an envelope dissolves the strict lane's signal for no fidelity gain)".
Two problems.

1. It is a **testing-convenience argument**, structurally identical to
   the R1 "no oracle exists" argument broken in §1.2 — and phase 0's
   rule is that a KEEP needs a fresh argument under the new goal, where
   the upper-bound claim owns exactly these rows (the spec fixes no
   panic text, no exit class, no fatal-message wording; every one of the
   nine is a modeled singleton inside a permitted set).
2. The premise "an envelope dissolves the strict lane's signal" is
   **refuted internally**. The project already built and ruled the
   technique that keeps the signal: the **R-1 ruling**
   (`docs/2026-08-20_w32-re-envelope-charter.md:335-394`) — *the forced
   half is compared exactly and stays strict; the TEXT is quotiented* —
   and executed it on four rendering rows (`BUGS.md:145-152`,
   `raft-w43-log.md:397`). The apparatus already ships text quotients in
   production: deadlock and race rows compare **fixed canonical
   messages** and their real content is the machine-side ∀-path claim
   (`diff-coverage:490-511`).

So each of the nine needs either the R-1 treatment or a written per-row
reason why R-1 does not apply. My read after the exercise: R9/R10/R11/R12
and C9 are R-1-shaped (forced half + quotiented text) and should be
converted, not grandfathered; E8/E10/R5/R8 are value-or-order pins where
the R-1 shape does not obviously apply and a per-row argument is owed.

### C-2 — KEEP-WEAKENED

The labeling in `NPDRF.lean:31-48` is exemplary ("no theorem in the repo
claims it, nothing may cite it … it is refutable as written"). But
doctrine **register #5** (`essence-of-go-doctrine.md:134-142`) states
the soundness condition and routes the residual to "the NPDRF/reduction
line's territory — the mover theorem **resumes** over the WIDENED point
set", with no hint that the discharge is an unproved, refutable draft;
and C's own crosswalk still classifies the row `ARGUED-AWAY
(incomplete)`. Honest labeling that lives only at the code site, while
the citing documents read as a discharge, is the same failure shape as
C-F1's off-repo theorem citation. Surviving condition: move the label to
register #5 and to the crosswalk's class column (`PINNED-with-planned-
discharge`, not `ARGUED-AWAY`).

### C-3 — KEEP-WEAKENED

Leg one verified: `Choices.consume` maps every stream value into the
menu (`State.lean:151-160`, `c % max 1 bound`), the single tagged
combinator `consumeAt` is the only interpreter path
(`State.lean:263-266`), and the site census is exhaustiveness-checked
(9 constructors, `:207-213`). Leg two does not hold as stated: the KEEP
says exhaustion yields "the canonical member, slot 0, **whose meaning is
DECLARED per site** in `ChoiceSite.policy`". `SitePolicy.canonicalSlot0`
is a **`String`** (`State.lean:233`), described in its own docstring as
"docstring-checked", and the table's provenance line (`:235-237`) says
every row "transcribes the pre-Q1 code's exact behavior at its site" —
the declaration was derived FROM the code it is meant to constrain, so
it cannot detect a drift in that code. Surviving condition: C's own
REOPEN(S) trace validator, plus the cheapest possible test — for each of
the 9 sites, empty-stream behaviour equals slot-0 behaviour.

### C-6 (fuel) — KEEP-WEAKENED

**Attack refuted:** see B13 above — fuel-out genuinely cannot become an
observation, and the dedup/nonterm combination is refused fail-closed.
The claim-level ruling is sound. Two weakenings:

- `--allow-nonterm N` **replaces the run fuel** (`CLI.lean:1450-1453`),
  so a branch that would terminate in more than N steps is bucketed
  identically to a divergent one. On the one live row N=200.
- The `nonterm` tally is written to stderr (`CLI.lean:1591-1595`) into
  `enum-stats.txt`, which `diff-coverage` reads back **only on failure**
  (`:1169`); the membership PASS record (`:1282-1286`) reports
  members/enumerated/exhibited/unexhibited/samples and not the nonterm
  count. So on a green row the number of pruned branches never reaches
  `latest.tsv` or the baseline. Combined with A3-Q2's unruled OQ5 this
  is "a number no gate can check" already in production on one row.

### C-7 (register #7) — KEEP-WEAKENED

C escalates a framed (a)/(b) choice and recommends (a) KEEP-with-rider.
I have no break to add: the too-wide direction is transfer-safe as
argued, and the observed-∉-modeled direction (gc's `maxAlloc` panic) is
correctly identified. Surviving condition, stated more strongly than C
does: (a) is only a KEEP if the domain-condition rider is **mandatory**
on every claim and the row is re-labelled a PIN-to-success in the
crosswalk — otherwise it inherits "standing idealization" status minted
under the old goal, which is what the mandate forbids.

---

## 6. Lane D — 5 KEEP rows

| row | verdict | one-line reason |
|---|---|---|
| D-1 fast-gate scope caption | KEEP-WEAKENED | `[stale]` on an `ok` line, plus an unreported results-redirect path |
| D-2 push/PR CI green ≠ corpus green | **KEEP-BROKEN** | no failure notification anywhere; the caption cannot carry the cadence claim |
| D-3 `GOLEAN_ALLOW_NO_DIFF` is a visible note | KEEP-WEAKENED | set unconditionally by CI itself; result is still PASS |
| D-10 per-lane statistical honesty | KEEP-WEAKENED | four caption items owed, three of them measured this session |
| D §1 exec-lane integrity ("known-good properties hold") | KEEP-WEAKENED | the listed properties hold; three fail-opens sit just outside the list |

### D-2 — KEEP-BROKEN → REOPEN (S)

D's disposition is "KEEP the design; add the caption to README/claims
documents (not to the gate)". Three facts make a caption an inadequate
remedy:

1. **The workflow has no failure notification of any kind.**
   `.github/workflows/lean_action_ci.yml`: no `if: failure()` step, no
   issue creation, no webhook/email. The only `always()` steps are the
   OOM `dmesg` dump (`:228-235`) and the cache save (`:246-253`). So the
   nightly `--slow` going red produces a red check on a scheduled run
   and nothing else. D-1/D-4's comfort — "bounded by the nightly, ≤1 day
   for pushed work" — is a *cadence* claim with no *delivery*
   mechanism; the bound is on when the check runs, not on when anyone
   learns.
2. **`tier=slow` is one row** (B12 above), so "the nightly is `--slow`
   (strongest form)" differentiates the nightly from `--diff` on a
   single corpus row. The nightly's real value is that it runs the
   differential at all — which is exactly what push/PR does not do.
3. **`GOLEAN_ALLOW_NO_DIFF=1` is set on every push and every PR, on all
   branches** (`:193`; `push:`/`pull_request:` carry no branch filter),
   and it downgrades both the differential and the negative baseline
   diff to notes while still returning `RESULT: PASS` (`ci:530, 598`).
   Composed with B12's one-directional flip guard, a commit that edits a
   baseline row `FAIL → PASS` passes CI green with nothing having run.

Minimum surviving form: the caption **plus** a failure signal on the
scheduled job (an `if: failure()` issue/notification step, S) — without
it the "certification cadence is nightly" sentence is not true in the
sense a reader will take it.

### D §1 exec-lane integrity — KEEP-WEAKENED

Every property D enumerates re-verified (no-record = FAIL; meta-less or
sha-mismatched record = FAIL; mode in banner; infra death publishes
nothing; unknown flag refused; worker death fails closed per row;
duplicate baseline rows flagged; typo'd Status/Pinned-by fail closed).
Also confirmed and worth adding as a strength: **the Lean CLI consumes
no environment variables at all** (no `IO.getEnv` anywhere) — every knob
is a flag, so the machine side has no env escape hatch.

Three fail-open paths sit immediately outside the enumerated list, and a
hostile outsider finds them in the same read:

- absent `go` ⇒ note ⇒ `RESULT: PASS` (`ci:179`; §4/B5 above);
- non-PASS → PASS baseline flips unguarded (`ci:661-667`);
- clean deletion of a failing case unguarded (no corpus-size ratchet),
  and untriaged ceilings raise silently (`check-bugs.sh:234, 278-281`).

Surviving condition: fold these three into D-4's REOPEN so the
"integrity kit" claim covers its own perimeter.

### D-1, D-3 — KEEP-WEAKENED

D-1: the `[stale]` suffix on an `ok` line is the named hazard, and one
more path belongs beside it — `GOLEAN_COVERAGE_RESULTS`/`_ARTIFACTS`
redirect where a run publishes (`diff-coverage:8-10`), while `ci:522,540`
read the **hardcoded** `artifacts/coverage/{negative-,}latest.tsv`, so a
redirected run silently leaves the previous record for the gate to
judge, with no note. D-3: the note is genuinely visible, but CI sets the
variable on every push and PR, so it is present in essentially every run
an operator sees — a speedbump that is always depressed. Neither is a
break; both are conditions on D-4's fix.

### D-10 — KEEP-WEAKENED

The per-lane claims are stated where they are made; the residual softness
is correctly classed as evidence-base limits. Four caption items owed
(D already recommends the first):

1. the strict lane's ≤10-pick prefix limit (streams are 10/10/8 entries,
   exhaustion → default);
2. the strict invariance check compares the three streams against the
   **default (empty-stream) run**, not against the oracle
   (`diff-coverage:766-783`, primary run at `:691` passes no
   `--choices`), and it **discards the variant run's exit status**
   (`if variant_obs="$(...)"; then :; fi`) — a failing machine run under
   a variant stream is reported as `nondet`, i.e. mislabelled (still
   fail-closed);
3. 10 of 25 membership rows carry no `members=` cardinality pin (B13);
4. the 21 racy + 19 deadlock rows compare constant strings, so their
   differential content is status-class only — their real content is the
   machine-side ∀-path claim, which is worth saying explicitly.

---

## 7. What I could not break (recorded, because the attacks were the obvious ones)

1. **Full stenciling is not a totality risk** — `mono.go:819`'s registry
   cap refuses by name; the collision registry (`:807-818`) refuses
   non-identical types under one key. §3/A3-D3.
2. **No confluent `|set|=1` row can silently drop a fuel-cut branch** —
   `nonterm=` is membership-only and refused under `engine=dedup`;
   without the flag a fuel-cut branch is a hard error. §4/B13.
3. **The stdlib injection scan is types-based, not text-based** —
   aliased imports, `defer`-position calls and calls inside generic
   stencils all inject correctly. §3/A3-S7.
4. **`check-bugs.sh` checks Cases polarity, not presence** — A2-B6's
   KEEP is stronger than it claims.
5. **`strings.Repeat`'s negative-count panic is verbatim upstream**, and
   the upstream-faithful-panic vs golean-refusal split
   (`stdlibshim.go:120-132`) is a genuinely good design.
6. **The zero-result subject guard** (`coverageharness/main.go:318-321`)
   forbids a value-free `ok` row — a fail-closed guard the channel map
   should advertise.

## 8. Routing summary

New REOPEN/ESCALATE items this pass generates, by cost:

- **S**: unsafe-surface refusal (§1.1); `ci:179` absent-`go` ⇒ FAIL;
  `coverage-negative` pin check; non-PASS→PASS flip guard; corpus-size
  ratchet / untriaged ceiling history check; nightly failure
  notification (D-2); the `funcVal` refusal message (§1.3.1);
  `GOARCH=386` compile leg (§1.2); Value.lean width caveat;
  empty-stream = slot-0 test (C-3); re-stamp the trace-coverage park
  (A3-Q3); A2-Q3's owner.
- **M**: the R-1 conversion sweep over C-13's nine rows; the mangling-
  surface ↔ frontier-queue tripwire (A3-D3); the DEMONIC-row grade
  restatement and R2/E9/C3 re-envelope obligations; A2-L1's delegation
  restatement + a go/types-vs-types2 agreement probe.
- **ESCALATE**: whether the 386 leg (compile now, execution when the
  environment permits) supersedes B8's second-implementation
  sequencing for the width question specifically; C-7's (a)/(b) framed
  choice with the rider made mandatory.

Environment item for the user (not worked around, per the sandbox
rule): 32-bit binaries abort here (`GOARCH=386` build succeeds,
execution → exit 133). If a 386 execution leg is wanted, that needs a
host/sandbox capability decision.

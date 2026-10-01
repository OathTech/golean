# The native `Intn`-style pick site — design (window unit 5b)

[AGENT] worker, lane `core/intn-pick-0930` (off `main` @ `bc91aa39`), 2026-09-30. Authority: [USER] Mike 2026-09-30,
verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Yes, I also prefer A, as long as it could be made
faithful», item (2) of `docs/2026-08-31_qrow-rulings.md` «The raft-proofs team's subject-delta note (2026-09-30) — RULED»:
a GENERAL native pick site — a value in `[0, n)`, a panic if `n ≤ 0` — inside the window, before the single re-pin;
execution table `docs/2026-09-24_window-plan.md` §4 unit 5b. The three teams' notes are design input, not positions
([USER], same day). Every decision below is [AGENT], PENDING [USER] ratification at the merge ask; none changes an
existing row's observations or takes a (b) pin (the whole-corpus choice trace is the check).

## 1. What Go says at the pin (go1.26.5, `deps/go/src`)

`math/rand.Intn(n)` = `globalRand.Intn(n)`; `(*Rand).Intn`: `if n <= 0 { panic("invalid argument to Intn") }` then a
uniform draw in `[0, n)` (`rand.go:178–181`). `math/rand/v2.IntN` likewise, text `invalid argument to IntN`
(`v2/rand.go:191–193`). Both panics are `panic(string)` — a PLAIN string payload, not a `runtime.Error`
(`recover().(string)` answers true). raft's `(*lockedRand).Intn` (upstream `raft.go`) draws
`rand.Int(rand.Reader, big.NewInt(int64(n)))` — `crypto/rand.Int` panics `crypto/rand: argument to Int is <= 0`
(`crypto/rand/util.go:73`) — and returns `int(v.Int64())`; its one call site `resetRandomizedElectionTimeout` passes
`n = electionTimeout ≥ 2` (`Config.validate`: `ElectionTick > HeartbeatTick > 0`), so the panic path is unreachable in raft.

## 2. The options

- **A. One general DRAW op + the callee's guard in the lowering (RECOMMENDED).** `Stmt.randIntn (target : Option
  Assignee) (n : Expr)` rides the wide-statement machinery (`StmtOp.randIntn`, one `stepFn` apply position, the
  existing `Step.stmtOpApply` rule); the apply consults `ChoiceSite.intn` at bound `n` (`n = 1` → 0 without a pop,
  `consumeAtE`'s uniform rule) and stores `.int pick .int`; domain `n ≥ 1` — a bypass is `stuck` by name. The frontend
  binds `math/rand.Intn` and `math/rand/v2.IntN` to the wire node `rand-intn` (callee-tagged), hoisted like `sync-op`; the
  DECODER expands `x := rand-intn(e)` to `$n := e; if $n < 1 { panic("<callee's text>") }; randIntn x $n` — upstream's own
  guard statement, a language-level `panic(string)`, so the payload CLASS is right for free and the text is the callee's.
  The op is callee-independent: any future callee with the `[0, n)` contract binds to the same site with its own guard.
- **A′. The panic inside the op.** Rejected: an apply's `.panic msg` is delivered as `panicEntry` = a `runtime.Error`
  box (`Machine.lean` `deliver`), so `recover().(string)` would be a WRONG ANSWER; making it a string panic needs a
  payload-class parameter on `deliver` and the `stmtOpApply` rule (a `Step` shape change) or an own `Frame` — cost with
  no fidelity gain over A.
- **B. Retire D-11 to upstream's VERBATIM body.** Measured (`scripts/lower-diagnose`, `.tmp/probe4`): four refused
  keys — `crypto/rand.Int`, `crypto/rand.Reader` (an unmodeled package VARIABLE), `math/big.NewInt`,
  `math/big.Int.Int64`. It needs a `*big.Int` value representation (a shadow type, or `math/big` source-through —
  its closure reaches `fmt`, `math/rand`, `strconv`, `sync`, assembly-twinned `arith_decl.go`) plus `crypto/rand.Int`
  as an environment contract over it and a stand-in for `Reader`. Well over one session → POSED, not taken (plan §4:
  «the re-keyed patch is the interim either way»).
- **C. A raft-specific native for `(*lockedRand).Intn`.** Excluded by the ruling (GENERAL, not raft-specific).

## 3. Decisions (all [AGENT], PENDING [USER] ratification at the merge ask)

- **D1** Option A. `ChoiceSite.intn`, canonical slot 0 = the value 0 (the empty/exhausted tape draws 0; bound = `n`
  exactly; `n = 1` pops nothing; `n ≥ 2` always pops — a DATA pick, not a scheduling pick).
- **D2** The `n ≤ 0` panic is the LOWERING's guard statement (upstream's text, per callee), not the machine op's arm;
  the machine refuses a bypass (`n ≤ 0` at the apply) as `stuck`, naming the forged-wire cause.
- **D3** Callees bound: the package-level `math/rand.Intn` and `math/rand/v2.IntN` (Go `int` result). The method
  forms `(*math/rand.Rand).Intn` / `(*rand/v2.Rand).IntN` (listed in plan §4) are NOT bound: a `*Rand` value needs
  `rand.New`/`NewSource`, outside the modeled surface, and a nil `*Rand` dereferences inside gc — they keep today's
  by-name package quarantine. `Int63n`/`Int31n`/`Perm`/`Shuffle`/… stay quarantined (other contracts).
- **D4** The target-less form (`rand.Intn(5)` as an expression statement, `_ =`) still DRAWS (Go does).
- **D5** Register: a third library-origin `primitive` row `rand-intn`; the cap 2 → 3. The register's own rule says a cap
  move is [USER] re-ratification — the ruling admits the op, the number is what is posed here.
- **D6** D-11 RE-KEYED: `(*lockedRand).Intn`'s body becomes the lock, `v := rand.Intn(n)` (`math/rand`), unlock; the
  import `crypto/rand` → `math/rand`, `math/big` dropped. Same envelope `[0, n)`, uniform on both oracles (the old
  map-range idiom's distribution delta is gone); the twin wire moves (reason recorded at the pin check).
- **D7** No new `Step` rule (the apply is `stmtOpApply`'s); the logic team's «one step rule» is a DERIVED lemma: for
  every `i < n` the singleton tape realizes the draw with label picks `PickRecord.ofPick .intn n i`; pinned in
  `BridgeSet` beside the apply equation and the `n = 1` no-pop equation, added to the core audit's required list.
- **D8** The dedup engine refuses the site (fail closed, like `tryLock`); the default enumerator carries the rows.

## 4. What D-11 becomes; what stays a delta and why

D-11 stays a recorded delta, smaller: upstream `rand.Int(rand.Reader, big.NewInt(int64(n)))` + `int(v.Int64())` →
`rand.Intn(n)` (`math/rand`). Residual: (i) the callee — `crypto/rand` entropy vs `math/rand`'s generator: unobservable
(the semantics is the envelope `[0, n)`, both uniform); (ii) the `n ≤ 0` failure text — `crypto/rand: argument to Int is
<= 0` vs `invalid argument to Intn`, both `panic(string)`; UNREACHABLE in raft (§1). Retiring it fully is option B.

## 5. Acceptance

Born rows only in the baseline (a membership row over `Intn(n)` with several values and gc's draws inside, the `n = 1`
control, the `n ≤ 0` controls with the exact texts for both callees, a `recover().(string)` payload-class control, the
composed jitter shape over the native); no existing row's observations change; the whole-corpus choice trace vs `main`
identical except the born rows and the twin's election draw; `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` red
only on the 5a pair; elaboration inside G-C3's 1.5× stop rule; `derive.py --check` clean; `check-stdlib-register` green.

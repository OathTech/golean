# Adversarial audit — Stage E (families E1–E4) of the evaluation-order model v2.1, branch `core/unseq-stage-e-0921` (candidate tip `3649b7db` over main `14006270`)

**VERDICT: FIX-FIRST** — one WRONG-ANSWER regression in the new E4 lowering (F1: `new(expr)`, a Go 1.26
form, inside an admitted sweep drops its initializer and any call in it — spec-forbidden member, strict default
≠ gc, main answers correctly), one decoder FAIL-OPEN (F2: `ref` of a `$` binder admitted as an invoke argument —
a callee can write a graph cell), one minor decoder FAIL-OPEN class (F3: unchecked `slice-lit` indices /
constant sizes turn malformed wires into Go-observable panics). Everything else audited holds: every member of
every flipped / moved / born set is spec-permitted and gc's draw is inside (20/20 per born package, my own
runs); the receive and method-call litmuses give exactly the spec-forced singletons where the spec forces and
the two-member envelopes where it does not; the two new machine body kinds are coherent (both directions),
store-neutral at the frame transitions and delegate to the legacy hoist statements (no raw memory op, no
footprint lie); the baseline delta is exactly 23 born / 22 changed / 0 PASS→non-PASS; 191 + 15 affected rows
and 241 outside-family rows reproduce on this box; the census reproduces (127 / 136 of 108 074); the gates I
could run are green (captured exits). Nothing in E5/E6 territory was touched (`emit.go` is not in the diff).

[AGENT] auditor, 2026-09-21, ordered by [USER] Mike («Dispatch the audit as you propose», relayed by the
[AGENT] coordinator). Worktree `.claude/worktrees/audit-unseq-stage-e`, branch `review/unseq-stage-e-0921`
at the candidate tip; the candidate's `.lake` copied at identical source (tree `0be0603a`), `scripts/capped
lake build` EXIT=0; candidate frontend `go build` (sha256 `13fda379…`), main's frontend from `git archive
14006270` (`0e3eff71…`); main's binary `/home/dev/projects/golean/.lake/build/bin/golean` (`0681abc6…`,
read-only), the candidate's (`6caf640d…`). No edit to the candidate or main; no push. Evidence:
`docs/evidence/2026-09-21_unseq-stage-e-audit/` (15 files, 84 KiB). Every logged decision below is
[AGENT]; the six ratification items (handoff §2) stay PENDING [USER].

## Findings, by severity

### F1 — WRONG-ANSWER (regression vs main): `new(expr)` inside an admitted sweep is lowered as `new(T)` — the initializer, and any call inside it, is silently DROPPED

What I did. The pinned spec (`deps/go/doc/go_spec.html` §Allocation, Go 1.26) admits `new(x)` with an
expression `x`; gc 1.26.5 accepts it. Litmus `docs/evidence/…/f1-new-expr-litmus.go`:

```go
func newExprVsCall() int { x := 1; m := func() int { x = 10; return 5 }; return *new(x) + m() }
```

gc: `6` (20/20 would be {6, 15} by spec: the read of `x` inside `new` is unordered against `m`). The
candidate's census admits the `return` sweep (`unseq 2 1 1`); the candidate frontend + binary answer **`5`**
(= 0 + 5): `*new(x)` yields the ZERO value. Main's frontend + main's binary answer `6`. Second litmus
`f1-new-call-dropped-litmus.go`: `return *new(m()) + x + h() + g()` with `m` printing `m` — gc prints
`m`, `g` and returns 110; the candidate prints only **`g`** and returns **103**: the call `m()` never runs.
Main: `m`, `g`, 110.

Why. `unseqMakeNew` (`tools/nativefrontend/unseq.go:814–862`) checks `new`'s arity and pointer result and
NEVER looks at the argument — no `tv.IsType()` test (the conversion arms at `unseq.go:602/975` have one), no
`unseqExpr` on it — so its reads and calls are not occurrences (census for `q := new(m())`: `events=1
calls=0`); `makeNew` (`unseq_lower.go:841–911`) emits `{"stmt":"new","value":{"expr":"default"},…}`
unconditionally. The legacy arm (`emit.go:9571–9614`) was fixed for exactly this («Go 1.26 accepts new(EXPR)
too … the original type-only arm silently default-initialized the value form (new/new-expr/eval-once caught
the expression never evaluating)») — the new lowering reintroduces the bug on the graph path. A
spec-FORBIDDEN member (5 ∉ {6, 15}), a strict default ≠ gc, a dropped side effect, fail-OPEN (the machine
answers where it should refuse or compute). No corpus row exposes it: the corpus's `new(expr)` uses
(`new/new-expr`, `imported-goose/semantics/new`, …) all sit in sweeps with no sibling call + observable, so
they stay legacy (my census: 127 admitted, one `new` — `assert-left-new-call`'s `new(int)`).

Where. `tools/nativefrontend/unseq.go:814` (`unseqMakeNew`, the `case "new"` arm),
`tools/nativefrontend/unseq_lower.go:841` (`makeNew`, `if name == "new"`).

Disposition (proposed). Fail closed now: in `unseqMakeNew` refuse `new` whose argument is not a type
(`tv, ok := e.info.Types[c.Args[0]]; !ok || !tv.IsType()` → `refuse("new with an expression argument (Go 1.26) — E5")`),
so the sweep stays on the (correct) legacy path; add the frontend unit witness, a wire mutant, and a corpus row
`evalorder/unseq-conv-alloc/new-expr-vs-call` ({6, 15}, membership) that RED-tests the refusal → PASS once E5
lowers the value form (classify the argument with `unseqExpr`; lower its wire as the `new` payload — an atom,
boxed atom or `struct-lit` head, which `unseqCheckPayload` already admits). Re-gate (`ci --diff`).

### F2 — FAIL-OPEN (decoder, D9): `unseqCheckArg` admits `ref` of a `$` BINDER cell as an invoke argument — a callee can write a graph cell

What I did. Mutant M10b (`docs/evidence/…/mutants.py`): the native wire of
`evalorder/unseq-recv-method/valueRecvVsArgCall` with `call2`'s callee rewired to
`$method$6:main.V0:Bump` (pointer receiver) and its argument replaced by `{"expr":"ref","id":"$u6"}` — the
V-typed binder cell that `read0` produces. The candidate DECODES and RUNS it (exit 0, value 11): `Bump`
incremented the binder cell `$u6` through the address. The graph's own rules forbid a cell being written by
anyone but its producer («duplicate result» — M7 refused; «a binder cannot be a store target» —
`unseqCheckTargetShape` refuses `.var "$…"`), and the frontend never emits `ref $…`; the decoder's contract
(fail closed on shapes the emitter never produces, Stage C design §5) is what is breached. The same arm shape
exists for func-value captures (`unseqCheckCallee`, `NativeToIR.lean:1025` — `ref` admitted with no `$`
check); M16 (`setG` with a `ref $u3` capture) stuck on arity, so the capture variant is a suspicion, not a
reproduction.

Where. `GoLean/NativeToIR.lean:1044–1058` (`unseqCheckArg`: `isAddr := … "ref" | "globaladdr" => true`, no
`id` check); `:1025–1037` (`unseqCheckCallee`, captures).

Disposition (proposed). Refuse a `ref` whose `id` starts with `$` in both arms, naming the cause («an
invocation argument / capture takes the address of a binder cell»); add mutants `mut-arg-ref-binder`
(+ a captures variant on a lifted-closure wire); `check-unseq-wire` ≥ 28.

### F3 — FAIL-OPEN (decoder, minor): `slice-lit` indices and constant sizes are not validated at decode — malformed wires answer with Go-observable panics

What I did. M11: `slice-lit` with `length: 1` and `elems[0].index: 5` — decoded; the machine PANICS
`index out of range [5] with length 1` (status `panic`, a Go-observable answer, not a refusal). M12: two
elems with `index 0` — decoded and ran silently (second store wins, value 15). M6: `make-slice` with the
constant `len -1` — decoded; machine panic `makeslice: len out of range` (a compile error in Go). The
frontend never emits these (a Go slice literal's keys are constant, distinct, in range; a constant negative
size is rejected by go/types); the legacy `makeSlice`/`slice-lit` statements share the property, so this is
a decoder-latitude class Stage E adds a path to rather than creates.

Where. `GoLean/NativeToIR.lean:2116–2130` (`"slice-lit"` arm: `length`, `elems` decoded without
`index < length` / distinctness); `:2094–2100` (`make-slice` `len` payload checked as an atom only).

Disposition (proposed). At decode: `0 ≤ index < length`, distinct indices (D-rule text: «the emitter's
literal is dense and keyed by distinct constants»); optionally refuse a negative constant size payload.

### F4 — RECORDS-CLAIM (trigger): «every other in-grammar sweep with a call has EVERY edge forced» is false for `string([]byte)` / `string([]rune)` on a private-but-aliased slice — a pin hidden as forced

What I did. Probe d1 (`probes-litmus.go`): `b := []byte("ab"); c := b; m := func() string { c[0] = 'z';
return "" }; return string(b) + m()`. Census: `legacy 1 1 0 — no non-event occurrence beside the call(s)
(legacy path: every edge forced)`. But the conversion READS `b`'s backing array, which `m` writes: the spec
leaves that read unordered against `m()` — {"ab", "zb"}. The legacy path realizes "zb"; gc draws "zb" (4/4
configs) — consistent with `order.go:1338–1356`, whose call class (`OSTR2BYTES`, `OSTR2RUNES`, `OLEN`,
`OCAP`, `OMAKE*`, `ONEW`, `OMIN`, `OMAX`, `OCOPY`) does NOT include `OBYTES2STR`. So: no wrong answer, no
differential red, but the classification is a (b) pin of gc's order presented as «forced»; the design's «a
conversion … cannot fail … never an occurrence of its own» (§E4) conflates "cannot fail" with "reads nothing
mutable". Inside an admitted graph the conversion node IS unordered: probe d2 (`b` captured by `m`) →
{"ab", "zb"} exact. The same for `string([]rune)` (a6: legacy, "zb" = gc).

Where. `tools/nativefrontend/unseq.go:763–812` (`unseqConversion`: no `d.occ` for the byte/rune-slice → string
forms).

Disposition (proposed). `d.occ(start)` for `string-from-bytes` / `string-from-runes` (a mutable read of the
backing array), which admits d1 with the set {"ab", "zb"}; or record the pin by name in the inventory
(E12 (b), «string(b) reads the bytes call-first on the legacy path»).

### F5 — RECORDS (spec-grounding of the `make`/`new` E1 participation): spec-defensible, but recorded as gc-grounded; the reading has consequences the records should state

What I did. Spec: §Order_of_evaluation orders «function calls, method calls, receive operations, and binary
logical operations»; §Built-in_functions: built-ins «are called like any other function». Under that reading
`make`/`new` (and `len`/`cap` — Stage C's rule, BUG-062) are ordered calls, and the strict row
`make-len-vs-call` is a spec-forced singleton (6; gc 6 on 20/20 here too). Under the other reading (only
user function calls are "function calls") the read of `n` inside `make([]int, n)` is unordered against `m()`,
{6, 8}, and the strict row is a (b) pin of gc's order. gc's `order.go` puts `OMAKESLICE/OMAKEMAP/OMAKECHAN/ONEW`
in its call class, so gc = the first reading. The design §E4 grounds the choice in gc («the control's gc draw
decided it»); the spec sentence is the grounding to record. Consequence to state: under that reading
`min`/`max`/`copy`/`append` are ordered calls too — today refused by name to the legacy path (probe k1:
`min(x, 100) + m()` → 1001 on gc and on both binaries — the legacy hoist happens to realize gc's early
`min`, reading `x` before `m`), so the inventory should say which reading governs the residue (E5).

Classification. (a)-by-spec-reading with the reading named; not a wrong answer either way. Disposition: one
sentence in the inventory's E2/E12 bullets + the design §E4 naming §Built-in_functions as the ground, and the
`min/max/copy/append` consequence as an E5 item.

### F6 — NIT (default-tape shape): interface-boxed literal payloads read LATE on the candidate's canonical order where main's legacy read them EARLY (= gc)

Probe a2: `[]any{x}[0].(int) + m()` — gc 6 (4/4: the boxing reads `x` before `m`), main 6, the candidate's
default 15 (set {6, 15} exact — membership-fine). A STRICT row of this shape would flip default ≠ gc; none
surfaced (my 191 + 15 + 241 rows all PASS; no admitted sweep in my census carries a boxed literal payload
beside a call). Record for E5's
`to-interface` payload family.

### F7 — NIT: the census counts lie for `new(expr)` (`q := new(m())` → `events=1 calls=0`) — subsumed by F1's fix.

### F8 — NIT: the decoder accepts an `after` edge on a composite-literal `allocate` (M8: set unchanged {6, 15} because the payload read is its own node). The design's «no E1 edge on literals» is frontend-only policy the wire cannot express (`new(T)` and `&T{}` are the same `new` spec); record as a design fact, not a defect.

### F9 — NIT (answer to the rename question): `alloc` → `allocate` is legitimate, not a footprint dodge

`check-mem-callsites`' token rule flags any identifier ending in `.alloc` (a constructor spelled `.alloc …`
in pattern matches hits `Store.alloc`'s token); the body itself performs NO raw memory operation —
`unseqAllocStmt` (`Machine.lean:2156–2166`) builds the SAME hoisted statements the legacy path executes
(`Stmt.allocNew` / `makeSlice` / `makeMap` / `makeChan` + element `assign`s), executed by the ordinary rules
under the wait frame; the two `Step` rules leave the store unchanged and emit `[]`. Inventory 70 rows PASS
here. The alternative (10 inventory rows with reasons) would have documented a non-site.

## (a) Member permission, per family — every flipped / moved / born row

Sets re-enumerated on this box (`scripts/diff-one`, candidate frontend + binary; `candidate-sets-affected-rows.txt`);
gc = my own 20 draws per born package (`gc-born-draws.txt`: GOMAXPROCS 1/8 × default/`-N -l`, 5 each) and the
lane's `gc-draws-e*.txt` for the E13/noodler rows (spot-checked 4 configs on the probes). Permission ground:
spec#Order_of_evaluation — only calls / method calls / receives / `&&` `||` are mutually ordered; «the order of
those events compared to the evaluation and indexing of x and the evaluation of y and z is not specified»;
the spec's own example `x := []int{a, f()} // [1, 2] or [2, 2]` (probe a5 → {12, 22} exact).

| family | row | set (candidate) | gc | each member permitted because |
|---|---|---|---|---|
| E1 | `unseq-globals/read-vs-call` | {1, 2} | 2 | package-var read unordered vs the call |
| E1 | `unseq-globals/compound-vs-call` | {2, 11} | 11 | the compound load is the same read; the store is phase 2 |
| E1 | `legacy-logical-vs-call/{or,and}-vs-call` | {`logical false 0`} strict | = | `\|\|` ordered before the later call (spec-FORCED) |
| E2 | `unseq-ptr-field-map/{deref,field,mapread}-vs-call` | {1, 2} ×3 | 2 | `*p` / `p.f` / `m[k]` reads unordered vs the call |
| E2 | `…/{deref,field}-compound-redirect`, `map-compound-rebind` | {11100, 10101} ×3 | 10101 | phase-1 operand values frozen (§Assignment_statements); hybrids absent |
| E2 | `noodler/latitude/deref-vs-call` | {11, 12} | 12 | deref unordered vs the redirecting call |
| E2 | `noodler/maps/compound-call-{mutates,deletes}` | {15, 105}; {(15,1), (5,1)} | 105; (5,1) | the load before/after the call's write/delete |
| E2 | `pointers/deref-target-rhs-call-order` | {92, 19} | 19 | the frozen pointer plan before/after the redirect |
| E2 | `builtins/len-vs-call-order/len-nil-only-none` | {10, 14} | 14 | the package-var read vs `wit4` inside the region |
| E2 | `e13/map-compound-index-key-vs-call` | {``·panic[5], `wit 5`·panic[5]} | `wit 5`·panic | the key's index panic unordered vs `wit` |
| E3 | `unseq-recv-method/recv-vs-read` | {2, 3} | 3 | the read of `x` unordered vs the receive and the call |
| E3 | `…/value-recv-vs-arg-call` | {6, 15} | 15 | the receiver copy is an operand «evaluated in the usual order» (§Calls) |
| E3 | `…/ptr-recv-vs-field-read` | {3, 4} | 4 | the field read unordered vs the method call |
| E3 | `noodler/latitude/receiver-vs-arg-call` | {6, 105} | 105 | as above (E14 sub-axis) |
| E3 | `e13/compound-call-target-vs-recv`, `map-compound-index-key-vs-recv` | witness {0, 1} ×2 | 0 | the target's load before/after the receive (phase 1 vs the ordered event) |
| E3 | `e13/map-compound-index-key-vs-method` | {``·panic[5], `M`·panic[5]} | `M`·panic | as the call row |
| E3 | `noodler/methods/nil-receiver-recursion` | confluent \|set\|=1 (dedup) | 10 | `Sum` mutates nothing |
| E4 | `unseq-conv-alloc/conv-read-vs-call`, `e13/bytes-conv-value-vs-mutating-call` | {98, 123} ×2 | 98 | `[]byte(s)` is a conversion, not a call: `s`'s read unordered (gc reads early — `OSTR2BYTES` in its call class) |
| E4 | `…/{struct-lit,addr-lit,slice-lit}-vs-call` | {6, 15} ×3 | 15 | the literal's payload read unordered vs the call (the spec's own example) |
| E4 | `noodler/latitude/{slice-literal-index,struct-literal-var}-vs-call` | {15, 1005} ×2 | 1005 | same |
| E4 | `noodler/latitude/conversion-index-vs-call` | {6, 105} | 105 | `int64(a[0])` pure over the unordered read |
| E4 | `e13/{composite-ptr-payload-vs-call,…-printroot,slice-lit-payload-vs-call,…-sinkroot}` | {``·panic[9], `wit 5`·panic[9]} ×4 | `wit 5`·panic | the payload's index panic unordered vs `wit` |
| E4 | `e13/slice-lit-payload-vs-recv` | strict `panic` | = | both orders one observation (unwitnessed channel) |
| E4 | `unseq-conv-alloc/make-len-vs-call` | strict 6 | 6 | F5: forced under «built-ins are called like any other function»; a (b) pin under the other reading |

No spec-forbidden member found. Extra probes (`probes-litmus.go`, 4 gc configs each): b3 `<-ch*100 + g + f()`
{101, 105} gc 105; c1 value receiver on a redirected pointer {6, 105} gc 105; c2/c3 nil receiver made non-nil by
the argument's call {panic, 6} gc 6; a1 nested struct literal {6, 15} gc 15 (decodes — the inner literal is a
slot); a2 `[]any{x}[0].(int)` {6, 15} gc 6; E2 phase-2: nil-map compound = gc's `f`·panic exactly; nil-pointer
compound {panic, `mut`·panic (frozen nil), `mut`·6} gc `mut`·6 — the frozen-nil member is the spec's phase-1
operand evaluation, permitted.

## (b) Receives as events

b1 `<-ch + f()` (f drains the channel): {11} singleton, gc 11 — the receive is E1-ordered BEFORE the later
call (sent to legacy as all-forced: correct, legacy realizes it). b2 `f() + <-ch` (f sends on the empty
channel): {15} singleton, gc 15 — admitted (the captured channel's read is the observable), receive AFTER the
call. b4 `<-ch + x + m()` on an empty unbuffered channel: the `deadlock` refusal, not a member; the enumerator
flags the alias-guard probe as a member-class failure (fail closed). The receive is ONE occurrence (`recv`
binds its cell at delivery: `unseqRecvStmt = chanRecv (binds.map .var) ch elem`, `Machine.lean:2149`); the
channel operand is a separate read cell (`e3recv` wire: `read3 → recv4`). Compound-target RHS: the flipped
rows above.

## (c) Method calls and receiver sub-evaluation

c4 `v.Add(f())` (pointer receiver on an addressable variable; `f` writes `v.n`): {15} singleton — the address
`ref v` is frozen, the body reads `v.n` after `f` (spec-forced; gc 15; sent to legacy as all-forced,
correct). `receiver-vs-arg-call` {6, 105}: 105 is gc's (the value receiver is copied AFTER the argument's
call, 20/20 in the lane's draws); 6 is the copy before `f` — permitted
(§Calls «the function value and arguments are evaluated in the usual order»; the receiver is part of the
method value). c1/c2/c3 above: the pointer read / auto-deref / nil-check member set is right and gc's inside.
`(*p).M()` → `addr-of-deref` occurrence (code-read; not probed). Slice-element / field receivers for
pointer methods refuse by name (`unseq.go:1123–1135`).

## (d) The observability trigger — probes

| probe | classification (candidate census) | realized (cand default) | gc | verdict |
|---|---|---|---|---|
| b1 recv then draining call | legacy «no occurrence observable … every edge forced» | 11 | 11 | forced, correct |
| c4 frozen-address receiver | legacy «no non-event occurrence» | 15 | 15 | forced, correct |
| d3 `f(x) + g()`, g writes x | legacy (trigger) | 11 | 11 | forced, correct |
| d4 `len(s) + f()`, f appends | legacy (trigger) | 11 | 11 | forced under Stage C's `len` rule (= gc) |
| a3 `cap(make([]int,1,n)) + m()` | legacy (trigger) | 6 | 6 | forced under F5's reading (= gc) |
| d5 `sink(x \|\| b, change())`, x private | **unseq** (the guard's own occurrence is observable) | false | false | BUG-113's shape with a private test → graph, correct; main also false |
| d1 `string(b) + m()`, b aliased | legacy «no non-event occurrence» | "zb" | "zb" | **F4**: an unordered byte read classified as forced (pin = gc) |
| a6 `string(r)` runes, aliased | legacy | "zb" | "zb" | F4 |
| d2 `string(b) + m()`, b captured | unseq | {"ab","zb"} | "zb" | envelope, correct |
| k1 `min(x,100) + m()` | legacy «builtin min» | 1001 | 1001 | = gc (F5's residue note) |

Equivalence of the legacy path on the returned sweeps: the 94 sweeps' rows are in the SAME set of the lane's
trace and in my 241-row outside check (all SAME); `evalorder/unseq-const-cell/elem-assign-const-string` and
`goroutines/worker-pool/shared-feed` (returned rows in the DIFFER list) PASS strict here.

## (e) The two new machine body kinds

Both `recv` and `allocate` have `Step.unseqRunRecv/unseqRunAlloc` (`.run i` → `.exec stmt env (wait i)`,
store unchanged, trace `[]`) and `unseqRecvDone/unseqAllocDone` (`.wait i` → `.pick`, `st.set i .done`);
`stepUnseqNext` has the matching four arms; `stepFn_sound` (`stepUnseqNext_sound`), `step_complete`,
`step_complete_any_wf_aux` and the stream-oblivious lemma `stepUnseqNext_run_wait_stream` gain the four
cases (`MachineSound.lean` diff), `step_preserves_wf_loc` the two run cases via `unseqRecvStmt_locSup` /
`unseqAllocStmt_locSup` (`StateWf.lean`), `unseq_record_stable` / `unseq_done_permanent` the two done cases
(`UnseqSound.lean`). `HeapNormal`/`StateWf` at the frame transitions are trivial (no store change); the
hoisted statement's own steps are the pre-existing rules the legacy path already runs (`allocNew`,
`makeSlice` + element `assign`s), so their preservation and their emitted accesses are the legacy ones —
`allocate` itself emits nothing (a `peek`-class non-access is right for a fresh object; the element STORES are
emitted by the `assign` statements as user writes). No raw memory op added: `check-mem-callsites` 70 rows PASS
(F9). No escape hatch in the diff (`sorry|native_decide|axiom|partial|admit|unsafe|implemented_by|extern|decide`:
none added). `wellFormed?` requires 1–2 recv binders; the decoder exactly 1.

## (f) Decoder mutants (`mutants.py`, `mutants2.py`, `mutant-results.txt`; through the real CLI)

| # | mutant | result | class |
|---|---|---|---|
| M1 | `slice-lit` payload names an unknown binder `$u99` | REFUSED «unknown slot '$u99' mentioned by occurrence 'lit1'» | closed |
| M2c | `recv` on an int slot (list reordered) | machine `stuck` «expected channel value, got int 1» | closed (late, named) |
| M3 | `deref(globaladdr gid 9999)` | REFUSED «globaladdr gid 9999 out of range … declares 2 global(s)» | closed |
| M4 | `new`'s `struct-lit` with 2 args for a 1-field struct | machine `stuck` «struct main.T literal expected 1 field value(s), got 2» | closed (late, named) |
| M5 | `slice-lit` elem `bool` vs cell `[]int` | REFUSED «yields slice bool but cell … declared slice int» | closed |
| M6 | `make-slice` constant `len -1` | DECODED; machine `panic` «makeslice: len out of range» | **F3** (accepts an impossible program; Go: compile error) |
| M7 | `recv` binding the call's binder | REFUSED «duplicate result» | closed |
| M8 | `after: [call3]` on a slice-literal `allocate` | DECODED, ran; set {6, 15} unchanged | F8 (harmless; policy not on the wire) |
| M9 | conversion head type `int` vs cell `[]uint8` | REFUSED «head type … disagrees with cell '$u1'» | closed |
| M10a2 | invoke arg `ref $u14` (int binder) to `Bump` | machine `stuck` «expected struct value for field access, got int 7» | closed by type only |
| M10b | invoke arg `ref $u6` (V-typed binder) to `Bump` | **DECODED and RAN (exit 0, 11): the callee wrote the binder cell** | **F2 FAIL-OPEN** |
| M11 | `slice-lit` `index 5` with `length 1` | DECODED; machine `panic` «index out of range [5] with length 1» | **F3** |
| M12 | `slice-lit` duplicate `index 0` | DECODED, ran silently (15) | F3 |
| M13 | `new`'s value an `ident` atom | REFUSED «neither a struct literal over payloads nor a zero value» | closed |
| M14 | `recv` `elem bool` vs cell `int` | REFUSED «receive element type … disagrees with cell» | closed |
| M15 | `allocation` with an unknown key | REFUSED «unknown key 'extra' … exact-key discipline» | closed |
| M16 | func-value capture `ref $u3` on `setG` | machine `stuck` «setG expected 0 argument(s), got 1» | arity, not the arm (F2 suspicion) |
| M17 | invoke arg `ref s` (a slice local, Stage B F2 class) | machine `stuck` by type | the F2-class address is admitted; only the callee's type check stops it |

Not crafted: a payload referencing a binder from a SKIPPED guard region (needs a guard wire; the region
join rules of Stage C are unchanged by this branch).

## (g) Strict rows' default tapes

The lane's trace (`choice-trace-main-vs-e4.txt`): 3692 ids, 3613 byte-identical, 56 DIFFER, 23 ONLY_B. I
joined the 56 DIFFER ids with the baseline and my runs: 41 are in my 191-row run (all PASS in their pinned
lanes), the remaining 15 (`channels/*`, `evalorder/unseq-const-cell/elem-assign-const-string`,
`goroutines/worker-pool/shared-feed`, `imported-goose/*`, `maps/*`, `slices/*`, `spec-examples-*`, `structs/*`,
`race/negative-sync/overwrite-vs-trylock`) PASS here (14 strict + 1 racy; `focused-runs.txt`). The 5 strict
DIFFER ids (`legacy-logical-vs-call/*` ×3 — the fixed rows; `elem-assign-const-string`; `shared-feed`) PASS
strict, so their default = gc. Baseline delta (`git show 14006270:baselines/native-full.tsv` vs the
candidate's): 3705 → 3728, born 23, changed 22, lost 0, **PASS→non-PASS 0**; 11 FAIL→PASS flips (2 + 1 + 3 + 5),
11 stage moves (10 strict→membership, 1 strict→confluent) — exactly the claim; the `two-workers-own-chans`
engine move is params-only (stage unchanged), as claimed.

## (h) Coherence, totality, gates (captured exits, this box)

`scripts/capped lake build` EXIT=0 (96 jobs, warm). `check-mem-callsites` EXIT=0 (70 rows); `check-unseq-wire`
EXIT=0 (26 mutants); `check-wire-boundary` EXIT=0 (11 + 20); `check-bugs.sh` EXIT=0 (114 bugs; BUG-102/104/113
`Cases:` rows behave as claimed); `scripts/capped scripts/check-unseq-scheduler` EXIT=0 (35 theorems, classical
trio only); `scripts/capped bash scripts/check-core-audit` EXIT=0 (45 modules, 51 theorems, controls fire);
`scripts/capped lake exe gocore-eval-tests` EXIT=0 (the label-shape facts); `check-frontend-pins` EXIT=0
(twin wire = pinned bytes; 10 203 sweeps, 0 admitted in my census too). Escape-hatch grep on the core diff:
none. `stepFn_sound` / `step_complete` carry the same labels in both directions for the four new arms (the
proofs are `simp [stepFn, stepUnseqNext, hget, hbody]` on both sides).

## (i) Records

Census reproduced: candidate 127 / main 136 admitted of 108 074 corpus sweeps (`census-both-frontends.txt`).
Baseline delta as claimed (above). BUG-102/104/113 `Status: fixed` with `Cases:` = the flipped rows;
`check-bugs` ok. Latitude edits name exactly the moved/born rows (inventory diff: `receiver-vs-arg-call`,
`deref-vs-call`, `compound-vs-call`, `read-vs-call`, `compound-call-mutates`, `conversion-index-vs-call`,
`deref-target-rhs-call-order`, `len-nil-only-none`, `value-recv-vs-arg-call`, `nil-receiver-recursion`,
`two-workers-own-chans`, the `unseq-ptr-field-map` package). The six PENDING items each name an alternative
(items 1–2: stay (b) pinned; 3: the coarse trigger; 4: `depth=N` / raised DFS cap; 5: `make` without E1
edges; 6: a general `exec` body). The gate tails (`ci-slow-e{1..4}.tail.txt`) each show RESULT FAIL on
exactly `certificate provenance` STALE + the one `google-search` drift line — consistent with the 5a
protocol; I did not re-run `ci --slow` (not required; the focused evidence above stands in). One records
inaccuracy: design §E3 says «wit sits after len by E1» for the E13 deref/map rows — fine; §E4's ground for
`make`/`new` is F5.

## (j) Scope

`git diff --stat 14006270..3649b7db`: no `emit.go`, no legacy arm touched (`Stmt.unseqProbe`/`Cont.probeK`/
`ChoiceSite.unseqPanic` present and unchanged); no twin re-pin (`check-frontend-pins` ok); nothing in C3/C4/P
or the NaN lane. Outside-family behaviour: 241 rows sampled from baseline PASS rows outside the DIFFER∪born set
(≤ 2 per package, 120+ packages), exported with BOTH frontends and run on BOTH binaries (default tape):
241/241 identical observations (`outside-check.log`).

## What I did NOT check

- The full `scripts/ci --slow` on this box (relied on the four gate tails + 191 + 15 focused rows + the gates
  above); K=80 gc draws (mine: 20 per born package, 4 configs per probe).
- The qualified `pkg.V` spelling (no corpus row; the design records the gap).
- The func-value CAPTURE `ref $binder` arm with a real lifted closure (F2's second half is a suspicion).
- A payload from a skipped guard region (needs a guard wire).
- Choice-trace positional tags; `HeapNormal`'s lemma statement itself (argued from the store-neutral rules).
- The 94 returned sweeps' observations individually beyond the trace's SAME list and the 241-row sample.
- Whether any corpus row lowers `new(expr)` through the graph under a different admission path than the ones
  I enumerated (my census says none of the 127 admitted sweeps contains `new(expr)`).

## Proposed dispositions, summarized

1. F1 (must fix before merge): refuse `new(expr)` by name in `unseqMakeNew`, or classify + lower its value;
   witness + mutant + a corpus row; re-gate `ci --diff`.
2. F2: refuse `ref $…` in `unseqCheckArg` and `unseqCheckCallee`; two mutants.
3. F3: decode-time `index < length` / distinct indices for `slice-lit` (negative constant sizes optional).
4. F4: `d.occ` for the `[]byte`/`[]rune → string` conversions, or the pin recorded by name.
5. F5/F6/F7/F8: records — one sentence each in the design §E4 / inventory / handoff E5 list.
6. F9: no action.

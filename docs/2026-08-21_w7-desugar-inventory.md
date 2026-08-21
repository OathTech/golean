# The desugar-obligation inventory — W7 prep

**Status:** prep artifact for roadmap §W7 (SpecTec-Go: the AST-level spec and
frontend correctness). Docs-only; nothing here changes code, gates, or pins.
**Scope:** every semantic lowering decision the native frontend makes between
the type-checked Go AST and the GoCore program the machine runs. Each row is a
future **translation-validation proof obligation**: the thing a per-program
simulation certificate would have to discharge.

W7's plan of record is translation validation, not a verified elaborator —
per-program certificates that the spectec-AST semantics of the source and the
GoCore semantics of the emitted wire are in simulation. That only becomes
tractable if we know, before the tool lands, *what the lowering actually does*.
This file is that census.

**What this is not.** Not a bug list (though §10 names six holes, **two of them
now confirmed live silent wrong answers**), not a design proposal, not a work
plan beyond §11's ordering suggestion. Rows are descriptive: what the code does
today, at commit `4ef05649`, with verified anchors.

**Audit-fix round, 2026-08-21.** A pre-merge adversarial audit of the first
pass found, and this round fixed: the K2 register (wrong in three places and
under §0.2's own definition — see §13), an unsplit forced/latitude conjunct at
C-38, H-d's classification (now confirmed live, with a witness), a false
uniqueness claim at E-1, a false "no marker" claim at B-44, a Tier-0
recommendation that does not transfer as written (§11), three lowerings the
census missed (§3.9), and a dozen counts and anchors. Every correction in this
file is marked in place with the date rather than silently applied — a census
whose errors are invisible is worth less than one whose corrections are legible.

**Maintenance.** Anchors are line numbers at `4ef05649` and *will* rot. When a
row's code moves, move the anchor in the same change. When a desugar is
retired, delete its row and say so. When one is added, add a row — the census
is only useful if it stays total. Case families are given as prefixes, not
manifests; `baselines/native-full.tsv` is the authority on their colors.

---

## 0. How to read this file

### 0.1 The row schema

Every row carries six things:

- **Does** — one line: what the transform actually does.
- **Anchor** — `file:line`, verified at `4ef05649`; function-def line first,
  then the key inner lines.
- **Spec** — the normative anchor(s) the desugar implements, and where the
  reading is contested, the `docs/spec-interpretations.md` row or
  `docs/2026-08-11_latitude-inventory.md` entry that governs.
- **Must preserve** — the *shape of the correctness statement*: what a
  simulation certificate has to prove, stated operationally. This is the
  column that matters. "Correct" is not a proposition; "the hoisted prefix
  evaluates exactly the condition's ordered events, in order, before the
  branch" is.
- **Guardrails** — the differential evidence that exists today (case-family
  prefixes) plus the BUG ids whose fixes those families pin. A row with no
  guardrail is a row where a certificate would be the *first* check.
- **S/M/L** — a guess at the validation obligation's difficulty, not the
  desugar's complexity. L is reserved for obligations that are not value
  equalities: effect ordering, cell identity, frame scoping, dispatch
  selection, non-interference of an *untaken* path.

### 0.2 The five obligation KINDS (plus one sub-kind, K2m)

Not every row wants the same theorem. Mixing these up is the fastest way to
write a certificate that proves the wrong thing.

- **K1 · FORCED-order simulation.** The spec mandates an order; the lowering
  must reproduce it exactly. Statement: trace equality on the ordered events.
  Most of §2–§4.
- **K2 · LATITUDE realization (membership, not equality).** The spec leaves the
  order open and the *frontend* is the choice site. The certificate must state
  **membership in the envelope**, never equality with the current pin — pinning
  the pin into a theorem freezes a scaffold as a fidelity claim, which is
  exactly what the doctrine forbids. The frontend's ANF pass is the named
  realization point of latitude entries **E12** and **E13**
  (`docs/2026-08-11_latitude-inventory.md:672`, `:732`). The verbatim
  "**no GoCore choice site** — the frontend's A-normal-form pass" is **E13's**
  wording; E12 says the same thing differently ("call-first is a FRONTEND
  normalization, not a GoCore choice site") — the quote is attributed to one
  entry, the claim holds for both (attribution corrected in the 2026-08-21
  audit-fix round: the original text put one quote in both entries' mouths).
  The **K2 rows — 13, the corrected set** (audit-fix round; the membership
  question is the one the doctrine cares about, so this list is exact):
  **A-1** (the ANF pass itself, E12/E13), **B-6** (argument order among
  non-call operands, E12/E13), **B-19** (composite-literal element order,
  E12's census follow-on), **B-27** (`append` element order, same ground),
  **C-34** (call vs. assignment-target operands, E2 — the frontend's
  three-way *routing* selects which member of E2's envelope each arity class
  realizes, which is what makes this a frontend choice site even though E2's
  pin itself lives in the machine's call rules), **C-36** (map compound
  assign: target operands vs. RHS, E4), **C-38** (the pre/post-receive
  partition of a panicking non-call operand, E13), **C-40** (map element
  assign: base → key → value, E3/E4), **D-11** (file presentation order, E8),
  **F-2** (hidden-dependency init order, E7), **F-3/F-6/F-7** (the init
  schedule, L-011). Reading for "not specified": **UNSEQ**, per
  `docs/spec-interpretations.md` **I-2**.
- **K2m · MACHINE-side latitude (the frontend is NOT the choice site).** A
  sub-kind, split out in the audit-fix round because two rows were filed under
  K2 against §0.2's own definition. Here the envelope lives in GoCore and the
  frontend's obligation is the *dual* one: hand the machine everything the
  envelope needs and **never narrow it**. Certificates for these rows state
  preservation of the choice structure, not membership in an order.
  **C-7** (map iteration order — E9, re-enveloped 2026-08-19 machine-side) and
  **J-39** (select clause order feeding the machine's commit choice, C6/C7).
  Rows whose *own* obligation is forced but which carry a machine-side
  latitude note — **C-17** (multi-ready select commit), **C-30** (panic
  payload, R9/R10), **B-25** (negative make sizes), **B-27**'s append-growth
  half (R2) — stay K1 and say so in their notes.
- **K3 · LIBRARY-SPEC refinement.** For the shims there is no Go AST to
  simulate — the obligation is `REFINE(pkg.Fn, D)`: on the modeled domain `D`
  the shim's observable behavior (values, heap effect, panic value and
  occurrence, termination) equals the *documented* behavior of the real
  function, and outside `D` it refuses visibly. Differential testing gives a
  lower bound here and nothing more. §7.
- **K4 · PARTIALITY contract.** Quarantine stubs are not simulated; they are
  *absent*. Statement: "every call reaching this FuncId refuses visibly, and no
  other observable of the program changes" — plus, for methods, "the method
  table entry is exact, so satisfaction answers stay definite." §8.
- **K5 · WIRE well-formedness (emitter-side invariant).** The decoder assumes
  things of the wire. Each assumption the decoder does *not* check is an
  unguarded emitter obligation, and the certificate either discharges it or the
  decoder should start checking it. §9.

### 0.3 The architecture the certificate has to span

The lowering is **not** one component, and this matters for §12's first open
question. `wire.go:1-9` states the design intent: the wire is "a typed Go AST
(Go's grammar with go/types types attached and names resolved) … rather than
pre-desugared GoCore", keeping the emitter "a mechanical serializer" and
concentrating "the semantic GoCore mapping in Lean". That intent is real but
partial. The desugaring is split across three stages:

| stage | file | what it decides |
|---|---|---|
| **1. Go AST → wire** | `tools/nativefrontend/*.go` | ANF/hoisting, lambda lifting, goto restructuring, switch/select index machines, per-iteration loop cells, generics stenciling, fmt/shim substitution, quarantine |
| **2. wire → GoCore** | `GoLean/NativeToIR.lean` | range desugars, comma-ok recognition, breakable/labeled placement, declaration-then-assign, synthetic temps |
| **3. injected Go source** | `stdlibshim.go`, `importedmodel.go` | library models, re-entering stage 1 |

A per-program certificate must relate the **source AST** to the **GoCore
program**, so it spans all three; a certificate that stops at the wire proves
nothing about stage 2, and stage 2 owns real semantic content (the range
desugars, the comma-ok shape recognition at `NativeToIR.lean:1076-1091` via
`asMapGet?` (`:439-445`), the declaration-before-RHS ordering at `:1129-1136`
that §9 J-38 shows is load-bearing). Stage 3 is worse: a shadow package is type-checked and emitted
by a *fresh emitter run* and merged into the host wire (`importedmodel.go:183`),
so the certificate's subject program is not the one the user wrote.

---

## 1. Chapter A — the normalization core

Ten rows. Everything in §2–§4 leans on these; get them wrong and every other
row's statement is vacuous.

**A-1 · ANF statement-prefix splice — L — K1+K2**
- *Does*: each statement is emitted with a fresh hoist accumulator; effectful
  subexpressions bind to `$cN` temps in synthetic assigns spliced immediately
  before the statement.
- *Anchor*: `emit.go:2188` (`emitStmtList`), 2194–2204; design intent
  `wire.go:25-28`.
- *Spec*: spec#Order_of_evaluation. **This is the realization point of
  latitude rows E12 and E13** (`docs/2026-08-11_latitude-inventory.md:672`,
  `:732`), both of which name `wire.go:25` explicitly; reading I-2 (UNSEQ).
- *Must preserve*: for each source statement `S`, `[hoists; S']` performs
  exactly the effectful evaluations of `S`'s expressions, each temp holds the
  value that subexpression yields, `S'` reads temps instead of re-evaluating,
  and each temp is dead after `S`. **The order claim is MEMBERSHIP, not
  equality**: calls run before the non-call operand events of the same
  expression even when the non-call operand is lexically left (`a[i] + f()`
  with `f` mutating `i` yields a value where all-operands-left-to-right
  panics), which is inside the envelope but is not the only member — E13's
  table shows gc realizing a *different* member on the type-assertion axis.
- *Guardrails*: `binop-order/operand-panic-vs-call/*` (3, E12's pins); E13 is
  a census row with **no pin permitted**.
- *Notes*: a certificate that states trace *equality* against a
  left-to-right AST semantics is provably false here. The correct statement
  quantifies over the AST semantics' permitted set. Accumulators are saved and
  restored at **17 nested sites** (count corrected from "~10" in the
  2026-08-21 audit-fix round; derivation: every `saved := e.hoisted` in
  `emit.go` except `emitStmtList`'s own splice at 2194) — decl-stmt 3194,
  if-cond 3271, else 3297, for-condPre 3428, for-post 3445,
  per-iteration 3493/3553/3574, type-switch guard 4059, switch tag 4219,
  per-case 4305, funcLit 6286, short-circuit RHS 6516, select machine
  targets 8682/8701, select recv fallback 8768/8791. Every one of them is a
  place where the splice point of A-1's prefix moves, so the "each temp is
  dead after `S`" half of the statement has 17 non-trivial instances, not 10.

**A-2 · hoist temp binding and fresh-name discipline — S — K1**
- *Does*: binds an effectful wire node to a fresh `$cN` temp via a
  define-assign pushed onto the accumulator; returns an ident.
- *Anchor*: `emit.go:2213`; mint 2221–2229.
- *Must preserve*: the prefix binding evaluates the node exactly once; the
  ident denotes that value at every later read; names never collide within a
  program (`tmpSeq` monotonic).
- *Notes*: `tmpSeq` is program-wide and the H-11 dry run rolls it back
  (`emit.go:747`, `796`) so wires stay byte-stable — semantically inert
  alpha-renaming, but a certificate must treat temp names as bound, not free.

**A-3 · multi-value call splat — M — K1**
- *Does*: a tuple-valued call in forwarding position (`return f()`, `g(f())`,
  tuple-into-variadic) hoists to one multi-target call statement declaring
  per-result temps.
- *Anchor*: `emit.go:2238`; idents 2253–2264; refusals 2240, 2250.
- *Must preserve*: the call runs once; temp `i` holds result `i`; substituting
  temps for the tuple preserves values with no effect interleaved between call
  and reads — **and each temp is re-wrapped per destination slot**
  (`emit.go:6963-6970`).
- *Guardrails*: `interfaces/tuple-forward-boxing/*` — BUG-049 (raw temps into
  interface slots were a silent wrong answer).

**A-4 · `hoistForbidden` — the order-changing-position guard — M — K4**
- *Does*: marks positions where hoisting out would change evaluation order;
  every effect site checks it and refuses.
- *Anchor*: `wire.go:30-42`; readers `emit.go:2214, 2239, 5511, 5796, 5868,
  6027, 6081, 6536, 7574, 8205, 8270, 8301, 8458`.
- *Must preserve*: the guard is a property of the enclosing **statement**
  context and does not cross a function boundary (`emitFuncLit` clears and
  restores, 6292–6310).
- *Notes*: the field comment previously named a loop-condition setter that
  does not exist — corrected 2026-08-16 by the post-autonomy audit. **Today the
  only setter is the short-circuit RHS** (6520). Everything else is a
  forward-compatible fail-closed. Guardrails
  `bools/short-circuit-funclit` (audit R2A-F2: the over-refusal was invisible
  because a wrongly-`unsupported` case looks like a coverage gap).

**A-5 · `scHoistOK` — the short-circuit carve-out (E3 extension) — M — K1**
- *Does*: admits the single `hoist()` temp path while `hoistForbidden` is set
  for a short-circuit RHS; `emitBinary` captures those hoists and wraps them in
  the conditional.
- *Anchor*: `wire.go:44-52`; `emit.go:6517-6537`.
- *Notes*: the fidelity argument was written before the implementation
  (`docs/gallery-campaign-log/g2.md`, "E3 — THE FIDELITY ARGUMENT"). See B-1
  for the correctness statement.

**A-6 · func-literal hoist-context reset — S — K1**
- *Anchor*: `emit.go:6272-6297`, restore 6310. See A-4's note.

**A-7 · `fnHasRecv` len/cap hoist, with a panic-freedom refusal — M — K1**
- *Does*: in any function body containing `<-`, `len`/`cap` calls hoist so
  their spec-ordered position survives against hoisted receives — but only when
  the operand is syntactically panic-free; otherwise **fail closed**.
- *Anchor*: flag `wire.go:73-87`, set `emit.go:1529` / 6288 / 1271–1291;
  hoist + refusal `emit.go:7554-7563`; `panicFreeOperand` `emit.go:8403`.
- *Spec*: spec#Order_of_evaluation orders calls **and receives** lexically;
  latitude row E6 records the refusal.
- *Must preserve*: for panic-free operands the hoist is order-transparent (a
  commutation lemma keyed on a syntactic predicate); the refusal arm is a
  visible red, never a reorder.
- *Guardrails*: `channels/recv-order/*`, `channels/recv-order/dead-recv-len-operand`
  (permanent refusal) — BUG-023 (the need), BUG-026 (the flag must be
  FUNCTION-scoped or new emission paths rot it), BUG-032 (the panic-order
  regression), BUG-039 (`panicFreeOperand` missed implicit indirection through
  embedded pointer fields). **BUG-062 is OPEN**: receive-free functions still
  reorder inline `len`/`cap` against calls (`builtins/len-vs-call-order`).

**A-8 · lambda lifting: capture-by-reference as pointer parameters — L — K1**
- *Does*: a func literal becomes a synthetic top-level function whose leading
  params are pointers to captured variables; the expression is a func value
  carrying their addresses; reads become `*x$cap`.
- *Anchor*: `emit.go:6174` (`freeCaptures`), 6224 (`emitFuncLit`), 6236–6259,
  6328, 6379–6388; naming `wire.go:54-66`.
- *Must preserve*: two closures over one variable receive the same address;
  every read/write in the lifted body hits the same cell as the enclosing
  scope's variable; nested literals re-capture through the outer pointer
  param; lifted ids (`<FuncId>$litN`, mangled inside a stencil) are unique
  program-wide.
- *Guardrails*: `functions/closure-share`, `functions/closure-return-state`,
  `scoping/closure-shadow-binding`, `init/global-in-closure`,
  `panic-recover/recover-value`.
- *Notes*: three capture-set exclusions, each with a recorded reason —
  type-switch implicit bindings live in `Implicits` not `Defs` and were
  mis-captured as outer variables (caught by `recover-value`); `v.IsField()`;
  **package-level vars of any unit are never captures** (they resolve to
  `globaladdr`).

**A-9 · shadow-capture pre-binding — M — K1**
- *Does*: `x := x + 1` / `var x = x+1`: every RHS pre-binds to a hoisted temp
  evaluated in the *outer* scope before the declarations take effect.
- *Anchor*: `emit.go:2616` (`containsVarUse`), 2843–2861, 2964–2972;
  `var` form 3078–3090, 3135–3140; refusal 2906–2911.
- *Spec*: spec#Declarations_and_scope — a local's scope starts at the **end**
  of its ShortVarDecl/VarSpec.
- *Must preserve*: RHS reads resolve to the outer binding. Needed because the
  wire carries **names only** and the decoder emits `.initialization` for all
  declared targets *before* the assignment (`NativeToIR.lean:1129-1136`), which
  would otherwise resolve the RHS to the fresh zero cell.
- *Guardrails*: `scoping/block-shadow`, `scoping/switch-init-shadow`.
- *Notes*: this is the clearest example in the file of a **stage-1/stage-2
  joint obligation** — the decoder has no idea the hazard exists, the emitter
  compensates, and nothing checks the compensation. Found by a guardrail case
  (W2, 2026-07-24), not by any gate. One arm is still fail-closed rather than
  solved (`emit.go:2910`, self-shadowing define with a call RHS). Pre-merge
  audit 2026-07-25: the `:=` fix did not initially cover `var`.

**A-10 · synthetic-name namespace disjointness — M — K5**
- *Does*: stage 1 mints `$cN $tsN $tsvN $tsoN $swN $swiN $swfN $mvN $resN
  $lvpN $lvfN $pcN $gotoN $recv $litN $fmtN $aK $nilK $fK $deferClose<N>
  $deferRecoverNoop $pkginit $initN`; **stage 2 independently mints** `$rcoll
  $ridx $rlen $rfirst $roff $rnext $rrecv $rok $forFirst $blank{i} $cr{i}
  $cv{i} $mlv $mlok $ta $taok $lit $maplit $stub{i}`.
- *Anchor*: emitter `emit.go:2221, 4069, 4168-4169, 4232, 5518, 7815, 7793`;
  decoder `NativeToIR.lean:536, 543, 606-608, 883-895, 962-996, 1038, 1065,
  1089-1090, 1107, 1116, 1199, 1284`.
- *Must preserve*: no user identifier collides (free — Go's grammar forbids
  `$`), **and the two mints are mutually disjoint** (not free: it is an
  unwritten coincidence across two source languages, checked by nothing).
- *Notes*: cheap to make a real invariant (reserved prefixes, asserted at
  decode). Prime candidate for a mechanized side-condition rather than a proof.
  Adjacent: `$interface-method-unreachable` (`NativeToIR.lean:1339-1341`) is a
  reserved FuncId with **no** collision check — the duplicate-FuncId sweep
  (`:1395`) catches two such names, not one; a wire defining it converts a
  deliberate stuck into a silent call.

---

## 2. Chapter B — expressions

Forty-five rows. Chapter of the coverage ledger: "Expressions" (language
ledger §Expressions, ledger rows *Literals*, *Basic arithmetic*, *Assignment
and evaluation order*, *Pointers*, *Structs*, *Methods*, *Arrays*, *Slices*,
*Maps*, *Strings*, *Interfaces*, *Builtins*).

### 2.1 Control-flow-bearing expressions

**B-1 · short-circuit `&&` / `||` — L — K1**
- *Does*: pure RHS stays an inline binary node (byte-identical to pre-E3);
  effectful RHS normalizes to `$cN := x; if $cN { hoists; $cN = y }` (`&&`) /
  `if !$cN {…}` (`||`); the expression is the temp read.
- *Anchor*: `emit.go:6483`; guard 6517–6526; normalization 6530–6564; spec
  citation in-code 6496–6513.
- *Spec*: spec#Logical_operators ("the right operand is evaluated
  conditionally"); spec#Order_of_evaluation (binary logical operations are
  lexically ordered).
- *Must preserve*: LHS binds once, in order; the RHS prefix **and** the RHS
  execute iff the LHS temp is true/false; the temp's final value equals Go's
  `p && q`; nested short-circuits nest inside the outer conditional body.
- *Guardrails*: `bools/short-circuit-and`, `bools/short-circuit-or`,
  `bools/left-to-right`, `bools/short-circuit-effects/*`,
  `bools/short-circuit-funclit`, `comparisons/short-circuit`.
- *Notes*: the flagship control/data interaction — conditional execution of an
  arbitrary effect prefix. Everything else in A-4's refusal list exists to keep
  this position honest.

### 2.2 Calls

**B-2 · expression-position call hoist — S — K1** · `emit.go:6672`, 6680.
The call executes at its lexical position in the statement's left-to-right
effect order; the temp holds its single result. `effectful=false` for
conversions — see B-10's double-emission hazard.

**B-3 · static call by identifier — S/M — K1** · `emit.go:6827-6894`; Var arm
6862–6882; wire name 6859. The callee denotes the same object go/types
resolved; FuncId is path-qualified outside main (D-4). Stdlib objects stay
bare — the recorded dot-import defect shape (G-34).

**B-4 · call through an arbitrary func-typed expression — S — K1** ·
`emit.go:6830-6847`; func-typed field calls (incl. promoted) 7333–7351.
Callee expression evaluates first, then arguments.

**B-5 · immediately-invoked func literal — S — K1** · `emit.go:6787-6803`.

**B-6 · argument evaluation and variadic packing — M — K1+K2**
- *Anchor*: `emit.go:6961`; non-variadic/spread 7040–7069; fixed prefix
  7071–7084; **nil-slice** 7090–7096; pack loop 7097–7113.
- *Spec*: spec#Calls, spec#Passing_arguments_to_..._parameters,
  spec#Order_of_evaluation.
- *Must preserve*: each parameter receives the value boxed iff the slot is
  interface-typed; the variadic slot receives a slice of the packed tail in
  order — **`nil`, not empty, when the tail is empty**; a spread argument
  aliases the caller's slice with no copy. The pack itself is a hoisted
  slice-lit allocation, part of the caller's effect prefix.
- *The order half is MEMBERSHIP, not equality* (retagged K1 → K1+K2 in the
  2026-08-21 audit-fix round). "Arguments evaluate in source order" is
  spec-forced only for the arguments that are themselves **function calls,
  method calls, receive operations or binary logical operations** — the
  left-to-right rule's scope. A non-call argument's events (an index's bounds
  check, an assertion's type check, a deref) are ordered against a sibling
  call **only** by E12/E13's frontend pin, which realizes calls-first via the
  ANF hoist; E13 records gc on the *other* member for the assertion axis. The
  one direction that is forced, and is a BUG rather than latitude when wrong,
  is that a call's own arguments precede it ("g cannot be called before its
  arguments are evaluated") — the forced point **BUG-062** is open on.
- *Guardrails*: `variadic/*` (12 rows incl. `no-args-vs-empty-spread`,
  `spread-aliasing`, `forwarding`, `multi-result-call`).

**B-7 · tuple forwarding `g(f())` — M — K1** · `emit.go:6971-7037`.
`f` runs once; parameter `i` gets component `i`, boxed per slot; variadic
packing over temps equals packing over components. BUG-049.

**B-8 · generic call and generic func value — L — K1** ·
`emit.go:6805-6825`, 6901, 6923, 6363–6375; instantiation guards 4460–4473.
Resolves through `Info.Instances` to a mangled stencil FuncId. Rides E-23.

**B-9 · qualified source-package call / selector — S/M — K1** ·
`emit.go:7206`, 7267, 7184; routing 5420–5422. Qualified identifiers are name
resolution, not field selection; globals go through the same gid cell as the
owning package's own references (F-8).

### 2.3 Conversions and boxing

**B-10 · conversion `T(x)` dispatch — M — K1**
- *Anchor*: `emit.go:6686-6749`; byte/rune ops 6701–6721; bool retyping
  6723–6733; interface box 6734–6743; generic `convert` 6744–6748.
- *Spec*: spec#Conversions.
- *Must preserve*: the result equals the spec's conversion at the target type;
  `string`↔`[]byte`/`[]rune` allocate fresh backing where Go does; the node is
  **pure** — no effect, no panic beyond the machine-side op semantics.
- *Guardrails*: `ints/conversion-width-matrix`, `strings/*-conversion`,
  `structs/unnamed-conversion-targets` (BUG-020),
  `assign-order/conversion-call-eval-once` (BUG-047).
- *Notes*: **double-emission hazard.** `emitAssign` must not route a conversion
  RHS through the speculative `emitCallNode` (guard at 2893–2905): the
  conversion branch hoists inner calls as a side effect and then reports
  `effectful=false`, so `T(f())` called `f` twice — a silent divergence.
  Same guard for builtins (2883–2892, `copy-edge/eval-order`).

**B-11 · implicit interface boxing — L — K1**
- *Does*: one function boxes a non-interface value into an interface slot and
  retypes untyped `nil` into nilable non-interface slots.
- *Anchor*: `emit.go:2638`; subst-first 2641–2644; nil typing 2645–2675;
  box 2688–2696.
- *Spec*: spec#Assignability, spec#Interface_types.
- *Must preserve*: **every** assignable context that owes Go's implicit
  interface conversion gets exactly one box carrying the source's static type
  as the dynamic type; never double-boxes; nil interface stays nil.
- *Guardrails*: BUG-006 (raw values in interface slots), BUG-016, BUG-014,
  BUG-049, BUG-050 (`range/assign-form-interface-target`), BUG-051
  (`interfaces/call-assign-boxing`).
- *Notes*: L not because a site is hard but because the obligation quantifies
  over **37 call sites** (assign, return, args, map keys/values, struct/slice/
  array/map literal elements, send, case slots, comparisons, `new`, `append`,
  chan-recv and select delivery, the fmt error shim). Count corrected from
  "~25" in the 2026-08-21 audit-fix round; derivation: `grep -c
  'wrapInterfaceConversion(' tools/nativefrontend/*.go` = 38 at `4ef05649`,
  minus the definition at `emit.go:2638` — 36 in `emit.go`, 1 in
  `fmtdesugar.go:488`. All 37 funnel into the single `to-interface` producer
  (`emit.go:2696`), which is the one thing that makes the obligation
  tractable; `panic`'s own `wrap` key (`emit.go:7691`, C-30) is a separate,
  38th boxing decision that does **not** go through this function.
  A missed site is a silent raw store — that is four of the BUG ids above.
  **Two order pins in tension**: box AFTER hoist so the temp keeps the value's
  static type (2973–2975); box BEFORE hoist for map-compound keys so the temp
  sits at the map's key type (3909–3915).

**B-12 · mixed interface / non-interface comparison boxing — S — K1** ·
`emit.go:6572-6596`; switch case slots 4315–4343. BUG-017;
`interfaces/mixed-compare`.

### 2.4 Constants

**B-13 · constant folding — M — K1** · `emit.go:4424-4433`, 6341–6353.
Any non-ident expression with a go/types constant value emits the folded value
— `-7/3` never divides at run time. Spec#Constants makes this sound (constant
arithmetic is exact and compile-time). **Consequence for the certificate**:
runtime `QUO`/`REM`/`SHL`/`SHR` nodes always have a non-constant operand, and
the folding step must either trust or re-check go/types' constant evaluator.
Latitude R14 records constant precision as delegated/UNKNOWN.

**B-14 · constant materialization — M — K1** · `emit.go:6416`; float
6424–6436; int kind 6437–6451; string bytes 6455–6464; `exactRational` 6475.
Floats travel as **exact rationals** (single rounding at the machine's typing
boundary); integers carry the *underlying* kind (defined types resolve);
strings travel as raw **bytes** (JSON would corrupt invalid UTF-8); the float
test keys on the TYPE not the value kind, so `3.0` stores as an Int kind.
Guardrails `constants/*` (30 rows), `strings/string-escape-bytes`; BUG-042,
BUG-043 for the kind-defaulting class.

**B-15 · unary operators — S — K1** · `emit.go:6609`, 6630. Unary `+` is
dropped as the identity; `&` routes to address-of; `<-` to the receive hoist.

### 2.5 Index, slice, composite literals

**B-16 · index-get (array/slice/string) — S — K1** · `emit.go:5638-5665`.
Bounds/nil behavior is machine-side; string indexing yields the byte through
the same node.

**B-17 · index address `&a[i]` — S/M — K1** · `emit.go:5754-5772`. Array base
takes its address; slice base passes by value (the slice carries its base
location). Map element as target outside a single assignment fails closed
(5839–5842) — maps are unaddressable and this would otherwise die as a stuck.

**B-18 · slice expression, including 3-index — M — K1** ·
`emit.go:4516`; base 4520–4528; default high 4535–4567; max 4569–4575.
Array bases slice through their address (`a[:] ≡ (&a)[:]`, so slicing aliases
the array cell). Default `high` (**BUG-066 FIXED 2026-08-21, holes arc** —
this row's ⚠⚠ hole H-a: the old arm re-emitted the base as the `builtin-len`
operand, so a call-valued base ran twice, gc 1 vs machine 2, status `ok`): an
array operand takes its STATIC length constant (the spec's `len(a)` over the
one evaluated operand); a slice/string operand's `builtin-len` reuses the
SINGLE emitted base node — effects hoisted once, pure nodes byte-identical to
the old wire. Guardrails `slices/slice-elided-high-eval-once/*` (call base,
low-only sibling, explicit-high green control),
`pointers/slice-elided-high-pointer-array-base`,
`strings/slice-eval-order-elided-high`, plus the pre-existing `slices/*`,
`strings/slice-eval-order`, `pointers/pointer-array-full-slice` (none of which
covered an effectful base, which is how the hole survived).

**B-19 · struct literal (keyed / positional) — M — K1+K2**
- *Anchor*: `emit.go:5928`; pre-bind 5953–5974; declaration-order fill
  5975–6020; sync refusal 5929–5937.
- *Spec*: spec#Composite_literals; spec#Order_of_evaluation.
- *Must preserve* (K1): each field holds its (boxed) initializer or
  `default ⟦Field(i).Type()⟧`, and the **effects** of the element expressions
  occur exactly once each, in source order, despite GoCore's `structLit`
  taking declaration-order args.
- *The panic-order half is MEMBERSHIP* (retagged K1 → K1+K2 in the
  2026-08-21 audit-fix round): ⚠ the reorder is justified by `containsCall`
  (`emit.go:5917`) as the effectfulness oracle — "pure values need no temp;
  their evaluation moment is unobservable". That is only true for *effects*; a
  non-call **panicking** value (index, assert, deref) is not hoisted, so its
  panic can land out of source order against a hoisted sibling call. And here
  the latitude is **not** by omission — spec#Order_of_evaluation's own example
  block states it outright, with a composite literal:
  > `x := []int{a, f()}  // x may be [1, 2] or [2, 2]: evaluation order between
  > a and f() is not specified`
  (go1.26.5 pin; the two lines under it say the same for duplicate map keys and
  for map-literal key-vs-value). E12's census follow-on lists all three as
  **not yet censused**, so a certificate must state membership in an envelope
  nobody has written down yet, not equality with the current shape. §10 hole
  H-e —
  where the audit-fix round's probe result is recorded: on
  `S{A: arr[i], B: f()}` with `arr[i]` out of range, gc runs `f()` first, the
  same member the ANF hoist realizes, so the shape is not a *divergence*; it
  is an uncensused latitude point that happens to agree today.
- *Guardrails*: `structs/keyed-literal-eval-order`,
  `structs/positional-literal-eval-order`.

**B-20 · slice literal — S/M — K1** · `emit.go:6043`, hoist 6026;
constant-key refusal 6056–6058. Allocates a fresh backing of length
`max index + 1`; elements boxed; effectful elements hoist ahead of the
slice-lit statement (unobservable — the allocation has no user-visible effect
boundary, but the certificate must say so).

**B-21 · map literal — S/M — K1** · `emit.go:6080`; refusals 6081–6083,
6098–6100; nil-value typing 6118–6124. Entries insert in source order (last
duplicate key wins); key and value boxed per map type. BUG-016/BUG-014;
`maps/literal-eval-order`, `maps/map-literal-duplicate-*`.

**B-22 · array literal — S — K1** · `emit.go:6139`; constant-key refusal
6149–6152. A **value**, not an allocation.

**B-23 · `&T{...}` and elided `&T` — S/M — K1** · `emit.go:5793-5803`,
5862–5889, 5898. Fresh storage per evaluation. Both refuse under
`hoistForbidden`. `pointers/composite-literal-address`; arc-final audit F12
for the elided form.

### 2.6 Builtins

**B-24 · `len` / `cap` — M — K1** · `emit.go:7520-7564`. See A-7 for the
receive-bearing hoist and its refusal.

**B-25 · `make` (slice/map/chan) — S — K1** · `emit.go:8299`; slice 8313–8331;
map 8332–8342; chan 8343–8361. Hoisted allocation statement. Negative sizes
are the machine's recoverable panic. `channels/make-edge/*`,
`builtins/make-map-hint`.

**B-26 · `new(T)` and Go 1.26 `new(EXPR)` — S — K1** · `emit.go:7567-7615`;
expr form 7586–7605. Expression form evaluates its operand **exactly once** —
`new/new-expr/eval-once` pinned a silent default-init bug.

**B-27 · `append` — M — K1+K2** · `emit.go:8204`; spread 8225–8232; pack
8233–8250; string spread 8185–8187. Base first, then elements left-to-right.
`slices/slice-append`, `slices/append-self`, `slices/append-overlap-window`;
BUG-021 (the envelope was too narrow).
- *Two latitude halves, both membership, neither an equality* (retagged
  K1 → K1+K2 in the 2026-08-21 audit-fix round). (i) **K2, frontend:**
  base-then-elements-left-to-right is B-6's ground — spec#Order_of_evaluation
  orders only calls/receives/binary-logical, so the placement of a non-call
  element's panic against a sibling call is E12/E13's pin, realized by the ANF
  hoist. (ii) **K2m, machine:** shared-backing vs reallocation on spill is
  latitude **R2** (a declared pragmatic subset) and lives in GoCore, not here —
  the frontend's only duty on that axis is not to narrow it.

**B-28 · `copy` — S — K1** · `emit.go:8269`. `builtins/copy-edge/*` (7).

**B-29 · `min` / `max` — S — K1** · `emit.go:7620-7636`. Strict n-ary,
left-to-right. `builtins/min-max-edge/*`.

**B-30 · `recover()` in expression position — M — K1**
- *Anchor*: `emit.go:7637-7646` (effectful=true); statement position
  2328–2354; `panic` in value position refuses 7647–7650.
- *Spec*: spec#Handling_panics ("called directly by a deferred function").
- *Must preserve*: **hoisting must stay inside the same frame**, which is what
  makes the desugar sound; the mark-recovered effect happens at the source
  evaluation point relative to neighbouring effects.
- *Guardrails*: `panic-recover/*` (23 rows), `builtins/recover-outside-defer`,
  `defer/recover-normal-return`; BUG-015 (recover through a promotion
  wrapper — see E-18's `"wrapper": true` marker).

**B-31 · `delete` / `clear` / `close` / `slices.Sort` — S each — K1** ·
`emit.go:7696`, 7753, 8441, 7729; dispatch 2316–2401. `delete`: nil map is a
no-op that still evaluates both operands; interface key boxed before compare.
`slices.Sort` is exact at integer elements only because equal elements are
indistinguishable (latitude R13, declared-unobservable narrowing).
`print`/`println` in statement position **refuse** (2355–2368) — this was
previously a fail-open decoder rejection.

### 2.7 Receivers, promotion, method values

**B-32 · receiver auto-address / auto-deref — M — K1**
- *Anchor*: `emit.go:4644`; deref arm 4652–4662; as-is 4665–4667; addr 4668.
- *Spec*: spec#Calls, spec#Method_sets.
- *Must preserve*: the first argument to the receiver-first lowered method
  equals Go's *adjusted* receiver — a copy of the (possibly auto-dereffed)
  value for value receivers, the (possibly auto-taken) address for pointer
  receivers — with the implicit deref/address panicking at the spec's point.
- *Guardrails*: `methods/pointer-auto-address`, `methods/value-auto-deref`,
  `methods/value-receiver-via-pointer-var` (BUG-048: machine wrong-STUCK where
  Go auto-derefs), `methods/pointer-method-value-read`,
  `methods/pointer-receiver-{slice,array}-element`.

**B-33 · receiver-position implicit `&*p` — M — K1** ·
`emit.go:4684`; emission 4693–4698; rationale 4671–4683. For `(*p).M()` with a
pointer-receiver `M`, receiver evaluation panics iff `p` is nil, **at receiver
time, touching no memory**. BUG-063; `methods/recv-implicit-addr-deref`.
- *Notes*: **the sharpest store-order pin in the file.** The strict
  addr-of-deref is deliberately scoped HERE and NOT put in `emitAddressOf`'s
  `StarExpr` arm (5773–5790), which keeps the plain collapse because its
  consumers nil-check at their own spec points — five store-order pins
  (`assign-order/target-check-vs-rhs/nil-deref-target` and friends) went red
  when it was moved there. Any certificate for B-33 must carry that scoping.

**B-34 · explicit `&*p` — S — K1** · `emit.go:6630`, 6647–6662. BUG-056;
`spec-examples-decl/address-op-nil-indirection/*`,
`spec-examples-decl/addr-deref-nil-matrix/*`. Spec#Address_operators' eager
clause; gc realizes it as a `TESTB`, invisible to `-race`.

**B-35 · promoted receiver adjustment — L — K1** · `emit.go:5140`; walkers
4714, 4744, 4765, 5117, 5094. Four-way path algebra over value/address modes
with a panic point at each pointer hop. `valueRootedFieldAddr` is legal exactly
when the chain crosses an embedded **pointer** hop (audit F2 2026-08-05: the
first cut wrongly refused it, killing whole exports).
`embedding/*`, `methods/*`; BUG-007.

**B-36 · promoted field read / address — M — K1** · `emit.go:5618-5629`,
5722–5727, 4794. GoCore's field ops are single-hop; flattening happens entirely
here, with nil-pointer panics at each implicit deref hop, in hop order.

**B-37 · plain field select / field address — M — K1** · `emit.go:5391`,
5631–5635, 5728–5753. The read/address duality is where the struct-field-write
backlog class lived (comment 5732–5734). BUG-001.

**B-38 · method value `x.M` (concrete receiver) — M — K1** ·
`emit.go:5442-5551`; capture 5543–5551; type-param re-resolution 5453–5468.
Receiver evaluated and hop-adjusted **at method-value time**: a value receiver
is copied then (later mutation invisible), a pointer receiver's address is
captured (later mutation visible). Pinned by
`defer/defer-method-receiver-eval`, `defer/defer-pointer-receiver-live`,
`embedding/promoted-method-value/{snapshot,live}`.

**B-39 · interface method value — M — K1** · `emit.go:5470-5531`; nil-check
hoist 5510–5529. **Panics at creation** iff the interface is nil (itab load —
audit F6 refuted the panic-at-call reading); later invocation dispatches on the
dynamic type held at creation.

**B-40 · method expression `T.M` / `I.M` / `(*T).M` — M — K1** ·
`emit.go:5553-5614`; alias unaliasing 5584–5589 (delta-review R3, pinned by
`methods/alias-promoted-method-expression`); `(*T).M` over a value-receiver
method **refuses** (5610, deref adapter not modeled). Spec's
five-equivalent-invocations block.

**B-41 · declared function as a value — S — K1** · `emit.go:6363-6375`.

### 2.8 Comma-ok and assertions

**B-42 · comma-ok type assertion — S/M — K1** · `emit.go:2745-2768`.
Never panics; `v` gets the asserted value or the zero, `ok` the flag; on `:=`
both declare per `Defs`. Comma-ok assert reaching expression position (a tuple
type) fails closed (4489–4491). BUG-034, BUG-057.

**B-43 · single-result type assertion — S — K1** · `emit.go:4480-4510`;
`source` at 4501–4508. The node carries the operand's **static** interface type
because Go's failed-assert message names it and it is not recoverable from the
runtime value (audit 2026-07-31 finding 8).

**B-44 · map index and comma-ok map index — M — K1+K5**
- *Anchor*: `emit.go:5638`, map arm 5648–5663; interface key boxing 5649–5654;
  the 2-target form rides the **generic assign path** (2819 + 2958–2985) and
  the *decoder* recognizes the shape at `NativeToIR.lean:1076-1091` via
  `asMapGet?` (`:439-445`).
- *Must preserve*: 1-value read yields the element or the elem zero (nil map
  reads as empty); 2-value additionally yields presence, **from one lookup**.
- *Notes*: **the marker EXISTS — this row's original claim that the seam has
  "no explicit marker" was wrong, corrected in the 2026-08-21 audit-fix
  round.** The emitter tags the node `{"expr":"map-get", …}`
  (`emit.go:5663`, and again for the compound-assign read at `:3954`), and
  `asMapGet?` matches on that tag, requiring `base`/`index`/`keyType`/
  `valueType` through `StrictJson.field` — so a *malformed* map-get fails
  closed. What is implicit is not the tag but the **arity gate**: the decoder
  consults `asMapGet?` only under `lhs.size == 2 && rhs.size == 1`
  (`NativeToIR.lean:1076`), and the same tag under any other arity decodes as
  an ordinary expression through `decodeExpr`'s `"map-get"` arm (`:252`). So
  the real contract a certificate must discharge is a **biconditional over the
  gate**, in both directions:
  (i) *soundness* — a wire `assign` with 2 lhs, 1 rhs and a `map-get` RHS is
  emitted **only** for a source comma-ok map read (nothing else may produce
  that combination, and the emitter must never route a comma-ok map read
  through a shape that also has 2 lhs and 1 rhs for a different reason);
  (ii) *completeness* — every source comma-ok map read reaches exactly that
  shape. Direction (ii) is the cheaper one: a 2-lhs assign whose RHS is **not**
  tagged `map-get` falls through to the arity test at `:1093`, where
  `2 ≠ 1` fails the decode loudly, so a lost tag is a visible red rather than a
  silent answer. Direction (i) has no net at all and is the one a certificate
  owes. The four keys themselves are already discharged at the boundary.
  Guardrails `maps/map-comma-ok`, `multi-assign/comma-ok-forms` (BUG-034).

**B-45 · package-level variable read / write / address — S/M — K1** ·
`emit.go:1225` (`globalAddr` — the single choke point), read 6389–6406, write
target 3008–3025, `&global` 5686–5700, lvalue 5821–5832, qualified 7267–7284 /
3032–3049 / 5702–5721. Every reference form denotes the **same** gid cell, so
aliasing through `&global` observes direct reads
(`init/global-addr-taken`). The choke point is also H-11's poison site (F-12).

---

## 3. Chapter C — statements and control flow

Forty-four rows (41 in the first pass; C-42/C-43/C-44 added by the 2026-08-21
audit-fix round — see §3.9). Ledger chapters: *If and basic loops*,
*Range loops*, *Switch*, *Labels/break/continue/goto*, *Functions and returns*,
*Defer, panic, recover*, *Assignment and evaluation order*, *Channels*.

### 3.1 If

**C-1 · if-init scope and condition-hoist placement — S — K1**
- *Does*: when the condition owes hoists, the whole `if` is wrapped in an
  explicit block `{init; condHoists…; if}`; without cond-hoists the plain
  `init` key is kept (byte-identical legacy wire).
- *Anchor*: `emit.go:3247`; scoped accumulator 3267–3284; wrap 3311–3333;
  the decoder's matching scope `NativeToIR.lean:1157-1161` (`decodeIf`'s
  `init` arm wrapping `core` in a `.block`; anchor corrected in the
  2026-08-21 audit-fix round — the old `:1143-1153` pointed at `decodeVar`).
- *Spec*: spec#If_statements ("the init statement executes before the
  expression is evaluated"), spec#Blocks.
- *Must preserve*: init executes exactly once before **any** condition event;
  the condition's effectful events run after init, in source order, inside the
  implicit block; init-declared names are visible to the hoists, the condition
  and both branches; the wrapper block adds no observable scope effect.
- *Guardrails*: `spec-examples-stmt/if-init-hoist-order/*` (9),
  `spec-examples-stmt/init-hoist-relatives/*` (6, the non-affected relatives
  pinned green so a fix cannot regress them silently),
  `spec-examples-lexical/panic-values/panic-error`, `if/if-init-scope`,
  `if/init-before-condition`, `control-flow/goto-if-init-cond-hoist` —
  **BUG-058**.
- *Notes*: BUG-058 had three observable modes, two of which were **silent wrong
  answers** (`if x := a(); b() == x` ran `b` first). Two wire shapes exist for
  one construct; the certificate must handle both. For-init, switch-init and
  type-switch-init are structurally unaffected (`emitFor` routes cond hoists
  into `condPre` inside the loop node; `emitSwitch`/`emitTypeSwitch` append tag
  hoists after the init).

**C-2 · else-if lazy hoist localization — S — K1** · `emit.go:3291-3309`.
Hoists from a later condition in an if/else-if chain are re-emitted **inside**
the else branch, so they run only on the paths where Go evaluates that
condition. `if/else-if-first-match`.

### 3.2 For and range

**C-3 · plain `for` (condPre / post wrapping) — M — K1** · `emit.go:3336`;
`condPre` 3423–3440; post 3441–3458. Init once; per iteration `condPre` events
+ cond, body, post (post's hoists inside it); `condPre` re-runs on every test
including the failing final one. **The post-statement's placement is
decoder-side** (`NativeToIR.lean:1169-1171`), so this row spans stages.
`control-flow/for-*` (5 rows).

**C-4 · Go 1.22 per-iteration loop-var trigger — L — K1**
- *Does*: for a `:=` for-clause init, scans body **and cond and post** for
  (a) func-literal capture of a loop var, (b) any address escape (`&x`,
  array-slice of `x`, pointer-receiver method rooted at `x`); if any, reroute
  to C-5, else use the shared-cell plain path.
- *Anchor*: `emit.go:3345-3413`; `findAddrEscape` 1855; `addrEscapeRoot` 1775.
- *Spec*: spec#For_clause + reading **I-5** (the spec is version-conditional;
  our scope is the declared language version, go 1.26 ⇒ ≥1.22 semantics).
- *Must preserve*: **completeness of the trigger for cell-identity
  observability** — whenever per-iteration cells are distinguishable from one
  shared cell by the program, the desugar path is taken. This is a
  non-interference argument about the **untaken** path, exactly the class the
  audit doctrine says green gates structurally cannot see.
- *Guardrails*: `range/range-loop-var-capture`, `functions/*`,
  `control-flow/*` — **BUG-003**; audit F2 2026-08-04 and delta-review round 2
  (cond/post captures and all three addr-escape shapes were silent wrong
  answers: 333 where Go said 12).
- *Notes*: `defer f(i)` is deliberately fine on the plain path (args evaluate
  at defer time). Conservative corner at 1846–1850 (promotion through an
  embedded pointer field over-reports) — over-triggering is safe given C-5.

**C-5 · per-iteration carrier-pointer desugar — L — K1**
- *Does*: `{ i := init; $lvpN := &i; $lvfN := true; for { i := *$lvp;
  $lvp = &i; if $lvf {$lvf=false} else {post}; condPre…;
  if cond {} else {break}; body } }`.
- *Anchor*: `emit.go:3485`; fresh cell + pointer swing 3537–3551; post/flag
  3552–3572; cond→break 3573–3586; schema comment 3474–3479.
- *Must preserve*: iteration `k+1`'s variable is a **fresh cell** initialized
  from iteration `k`'s value at post time (spec: "declared before executing the
  post statement"); post runs on the fresh cell; `continue` re-enters at the
  top so the current cell's value propagates without a copy-back; `break` and
  `return` exit with no extra events; each capture observes exactly its
  iteration's cell.
- *Notes*: **cell-identity (allocation) simulation, not value simulation** —
  the hardest kind. The cond compiles to `if cond {} else {break}` *inside* the
  body, so a labeled `continue` re-runs cell-refresh + post + cond, which is
  Go's order; `emitLabeled` has a special arm (C-23) to re-attach the label to
  the inner `for` of this block shape.

**C-6 · range assign-form (`for i, v = range X`) — M — K1** ·
`emit.go:3616-3703`; source component types 3630–3650; refusals 3661, 3680.
Iterates with fixed `$rangeKey`/`$rangeVal` temps and assigns the outer
lvalues **key then value** at the top of each iteration. Targets must be
identifiers (non-identifier targets refuse — their operands would be frozen
instead of re-evaluated per iteration). BUG-050
(`range/assign-form-interface-target`: raw temps landed unboxed in interface
targets — a silent wrong answer).

**C-7 · range over slice / array / map / string / int — M — K1+K2m** ·
`emit.go:3758-3829`; node 3840–3850; `rangeVarName` 3598. Emits a kind-tagged
node; **stage 2 does the desugar** (`NativeToIR.lean:856-998`) — index-able
kinds to an index loop, map to the `mapRange` primitive. Collection evaluates
once at entry; the int form takes the **operand's** type (BUG-043's
`operandType`, fail-closed at `NativeToIR.lean:910-918`). Map iteration order
is latitude **E9** re-enveloped 2026-08-19 under reading **I-1**, machine-side,
not the frontend's — which is exactly why the 2026-08-21 audit-fix round moved
this row out of **K2** (whose definition names the *frontend* as the choice
site) into **K2m**: the obligation is that the `mapRange` primitive is handed
the LIVE map and that no narrowing of E9's envelope is smuggled into the
desugar, not that some frontend-chosen order is a member of one.
`range/*` (20 rows), `strings/range-*`.

**C-8 · range over `*[N]T` — M — K1** · `emit.go:3708-3757`. Index-only form:
the pointer evaluates once into a discarded temp and the range becomes
range-over-static-int `N` — never dereferences, so a nil pointer iterates fine.
Value form: pointer hoisted once, `kind:"array-pointer"`, elements read through
it each iteration (nil panics at the first read; in-loop writes are observed —
no snapshot). Pre-merge audit 2026-07-26 caught an up-front deref that
snapshotted. `range/range-array-pointer*` (3).

**C-9 · range over channel — S — K1** · `emit.go:3811-3825`; 2-var refusal
3817. Operand once; each iteration is one receive; exits on closed-and-drained.
`channels/range-closed`.

**C-10 · range-over-func — ABSENT — S — K4** · `emit.go:3826-3828`
(`unsup`). No lowering exists; the obligation is only that the refusal is
visible (it is: per-declaration quarantine). `range/range-func-*` are
frontend-blocked rows.

### 3.3 Switch

**C-11 · expression-switch selection-index desugar — L — K1**
- *Does*: `breakable{ block{ init; tagHoists; $sw := tag; $swi := defaultIdx;
  test-chain in TEXTUAL case order (each case's hoists nested under the earlier
  tests' else) setting `$swi`; $swf := false; dispatch-chain in SOURCE clause
  order, each `if $swf || $swi == i` running the clause body as a sibling
  block } }`.
- *Anchor*: `emit.go:4207`; tag temp 4218–4241; `$swi` 4289–4300; test chain
  4301–4359; dispatch chain 4364–4399; breakable 4404. Design:
  `docs/2026-08-04_control-flow-design.md`.
- *Spec*: spec#Expression_switches.
- *Must preserve*: the tag evaluates exactly once, after init, before any case
  expression; case expressions evaluate **lazily, left-to-right in textual
  order, stopping at the first match**, with their effects and panics timed
  exactly there; the selected clause is the first match else default wherever
  it sits in source; exactly one clause body runs modulo fallthrough; clause
  bodies are sibling scopes.
- *Guardrails*: `control-flow/switch-*` (14), `scoping/switch-*`.
- *Notes*: two chained index machines; the simulation invariant relates
  `$swi`/`$swf` valuations to "which clause Go selected / whether fallthrough
  is armed". Tagless switch uses the case expression as the condition
  (4314–4316), same laziness. Mixed interface/non-interface tag-vs-case
  comparison boxes both directions (4317–4343, BUG-017).

**C-12 · fallthrough flag — M — K1** · `emit.go:4260-4266` (strip),
4383–4396 (clear/arm), 4371–4374 (final-clause refusal). A trailing
`fallthrough` becomes `$swf := true` as the last statement of its dispatch arm;
every arm first clears `$swf`. **Must preserve**: fallthrough transfers to the
next clause body without evaluating its case expressions, and a body exiting
early (break/return/panic/continue) never reaches the arming assign — so the
proof content is exactly that "arming ≡ normal completion of a
fallthrough-terminated body". `control-flow/switch-fallthrough*` (2).

**C-13 · `breakable` scope — S — K1** · `emit.go:4404`, 4143, 8900;
break/continue emission 2518–2529. Switch, type switch and select each wrap in
a wire `breakable`; GoCore models it directly, so there is no flag desugar.
`control-flow/break-label-select`, `control-flow/continue-in-switch`.

### 3.4 Type switch

**C-14 · type-switch first-match if-chain — M — K1** · `emit.go:4025`;
guard temp 4059–4076; clause split 4080–4092; chain built innermost-first
4093–4144; multi-type OR 4113–4123. Guard once; first-match over **source**
order; the default sits at the innermost else.
- *Must preserve*: the per-clause `pre` statements (the comma-ok asserts) sit
  in the block wrapping each `if` level (4138), so a test at level `k` runs
  whenever levels `<k` failed. The proof must actually **discharge the
  effect-freeness and panic-freeness of the tests**, since the lowering
  evaluates them slightly more eagerly than a lazy reading suggests.
- *Guardrails*: `interfaces/type-switch-*` (14 rows).

**C-15 · type-switch case test — S — K1** · `emit.go:4151`; nil arm
4152–4159; comma-ok 4166–4180. `case nil` becomes an interface comparison so
typed-nil boxes compare unequal (`interfaces/type-switch-typed-nil`).

**C-16 · type-switch per-clause binding — S — K1** · `emit.go:4185`, 4125,
4128–4129. The implicit variable (go/types `Implicits`) binds to the asserted
value in a single-type clause and to the guard temp (interface-typed) in
multi-type / default / nil clauses; a fresh per-clause **copy**, not an alias.

### 3.5 Select

**C-17 · select entry-time operand evaluation — M — K1** · `emit.go:8823`;
send clause 8843–8865; recv shapes 8866–8891; bodies emitted first at 8831.
Spec#Select_statements step 1: exactly one entry-time pass evaluates every
clause's channel operand and every send clause's value, in **source** order,
regardless of which clause commits; within a send clause, channel before value.
Recv **target** operands are not evaluated at entry (C-18). Multi-ready commit
choice is the machine's (latitude C6/C7 under reading **I-7**: select's
normative basis is spec-only, no memory-model guarantee).
`channels/select-deterministic/*` (8).

**C-18 · select recv — machine delivery targets — L — K1** ·
`emit.go:8663` (`machineSelectTargets`; bail-outs 8666, 8679, 8690, 8698,
8709), 8726, 8739–8747. For assign-form recv clauses whose every target is a
plain non-blank lvalue needing no boxing and emitting **no hoists**, targets
ride the clause head and the machine realizes spec §Assignments' two phases
post-selection.
- *Must preserve*: target operands evaluate **only in the selected clause,
  after selection** (`unselected-receive-lhs-not-eval`), in lexical target
  order; stores land left-to-right after all operand evaluation; a map-element
  target's store precedes a later target's store panic.
- *Guardrails*: BUG-029, BUG-030, BUG-033, BUG-036 — `channels/select-recv-edge/*`.
- *Notes*: **any hoist-producing operand forces the fallback**, because a
  hoisted temp would evaluate at select *entry*, violating step 4. That
  condition is exactly the validity boundary of the plan.

**C-19 · select recv — temp fallback with a single write-back — M — K1** ·
`emit.go:8749-8813` (BUG-036 comment 8749–8755). Receives into fresh `$c`
temps on the clause head; at clause-body top, the user targets' operand hoists
then **one** multi-target assign writes value and ok (boxed). All `:=` forms
take this path. Blank targets still consume a temp slot.

### 3.6 Goto and labels

**C-20 · goto dispatch-loop restructuring — L — K1**
- *Does*: a body containing `goto` becomes
  `{ hoisted decls; $pcN := 0; $gotoN: for { if $pc<=0 {seg0}; if $pc<=1
  {seg1}; …; break } }`, segments split at top-level goto-target labels;
  `goto L` lowers to `{$pc = seg(L); continue-to $gotoN}`.
- *Anchor*: `emit.go:1923`; segmentation 1929–1961; emission 2087–2131;
  `goto` 2530–2550; entry points 1580–1584, 6300–6303. Design:
  `docs/2026-08-04_control-flow-design.md` stage 3.
- *Spec*: spec#Goto_statements, spec#Labeled_statements.
- *Must preserve*: a sweep starting at `$pc = k` executes exactly segments
  `k..end` in order (guards are monotone because `$pc` changes only via a
  `goto` that immediately continues to the loop head); `goto L` ≡ a jump to
  `L`'s segment with all intervening block/loop contexts unwound (the
  `continue-to`'s unwinding **is** the out-of-block jump); hoisted top-level
  variables keep **one** cell across sweeps, valid only under C-21's envelope;
  normal completion of the last segment breaks out.
- *Guardrails*: `control-flow/goto-*` (10 rows) + 6 negatives.

**C-21 · goto fidelity envelope — L — K4** · `emit.go:2012-2085`. Four
fail-closed rejections before restructuring: targets not at body top level
(1957–1961, 1633, 2540–2543); hoisted vars captured by a func literal
(2018–2039); hoisted vars address-escaped (2040–2053, via the same
`findAddrEscape` C-4 uses); hoisted names shadowing an outer same-named object
the body also uses (2057–2085).
- *Must preserve*: **these four checks together must imply that collapsing
  per-execution cells to one hoisted cell, and moving declarations to the body
  head, is observationally invisible.** Proving the envelope's *sufficiency* is
  the real obligation; each individual rejection is easy.

**C-22 · `degradeGotoDeclares` / `degradeGotoTarget` — M — K1** ·
`emit.go:1702` / 1683; blank arm 1718–1732; zero-value re-init 1734–1738;
called at 2115; key list 1746.
- *Does*: a post-pass over each segment's **top-level wire nodes**: `var` decls
  become blocks of plain assigns (init value, or an explicit default-value
  assign for `var x T`); `declare` targets of *source* names degrade to `var`
  targets; `$`-prefixed temps keep their declares; blank decls keep a scoped
  declaration so the initializer still runs per sweep.
- *Must preserve*: re-executing a segment re-assigns hoisted cells with exactly
  the source initializer's value (or the **zero value** for uninitialized
  `var`), matching Go's fresh-variable semantics under C-21's envelope; only
  top-level nodes are rewritten (deeper blocks re-execute wholesale with their
  own scopes, getting Go's re-declaration semantics for free); temps stay
  `declare` because they are born and die within one statement in one sweep.
- *Notes*: this is a **syntactic rewrite over the WIRE, not the AST** — so its
  key coverage (`target`/`okTarget`/`lhs`, the list at 1746) must be shown
  complete for every top-level node shape a segment can contain, and it is a
  completeness trap for every new wire statement. Audit F4 2026-08-04:
  degrading a blank decl to an assignment produced an unbound `_` — a machine
  **stuck**, not a boundary refusal.

**C-23 · labeled break / continue restructuring — M — K1** · `emit.go:1624`;
wrap 1642–1669 incl. the block-with-trailing-loop arm 1656–1666; break-to /
continue-to 2520–2529; `scanLabelUses` 1598 (does not cross func-literal
boundaries); decoder placement invariant `NativeToIR.lean:840-844`.
`break-to L` exits exactly the L-labeled construct; `continue-to L` re-enters
the L-labeled **loop's head** — which for C-5 includes cell-refresh, post and
cond. The label-on-inner-loop repair for desugared shapes is the fragile point:
any new statement lowering returning a block shape must be added at 1652–1668
or **fail closed** (1650, 1666, 1668, 1673).

**C-24 · inert label drop — S — K1** · `emit.go:1636-1641`. An unreferenced
label has no runtime meaning; a labeled empty statement becomes an empty block.
`control-flow/labeled-empty-statement`.

### 3.7 Defer, go, panic, return

**C-25 · defer registration — M — K1** · `emit.go:2440-2490`. Callee
expression and args are emitted **now** (effects via ANF before the defer
statement); the wire `defer` prepends the pending call to the frame chain, run
at frame exit in LIFO order with those saved values; a nil callee's panic fires
at invocation. `defer` in a loop registers once per execution — no special
case, it falls out of statement placement. `defer/*` (13 rows).

**C-26 · `defer recover()` no-op — S — K1** · `emit.go:2445-2455`, 7777–7793.
Lowers to deferring a synthetic empty `$deferRecoverNoop` — it does **not**
recover (spec: recover must be called *by* a deferred function, not *as* one)
but the drain still observes a registration.
`panic-recover/defer-recover-builtin`. **BUG-031**: the "already emitted" flag
was sticky across a quarantined declaration, so a later `defer recover()`
referenced a never-emitted function — hence the rollback set (H-2).

**C-27 · `defer close(ch)` — S — K1** · `emit.go:2462-2464`, 7799; name
qualification 7815. Operand evaluated now; the close (and any
close-of-closed/nil panic) fires at frame exit as the deferred invocation's
panic. **BUG-027**: bare `$deferClose<N>` names collided across functions
(`liftSeq` resets per function) — a whole-package error;
`channels/defer-close-two`.

**C-28 · defer sync-op wrapper — S — K1** · `emit.go:2468-2477`, 8107;
refusal 8128. `defer mu.Unlock()` / `wg.Done()`: receiver **address** evaluated
now, op at exit. `defer wg.Add(n)` / `once.Do(f)` fail closed — deferred-operand
threading is a recorded capability gap. The statement-position twins are
**C-43** (the ops) and **C-44** (`once.Do`), §3.9.

**C-29 · `go` statement — S — K1** · `emit.go:2491-2515`; builtin-callee
refusal 2498. All argument evaluation events belong to the **spawning**
goroutine's trace, before the spawn.

**C-30 · `panic(v)` payload boxing — S — K1** · `emit.go:7666`, docstring
7656–7665; dispatch 2320–2321. Untyped nil → bare nil (machine maps to
`*runtime.PanicNilError`; the oracle runs `GODEBUG=panicnil=0`);
interface-typed → bare; otherwise `wrap` carries the static type for the
to-`any` boxing. The **nil-payload semantics decision lives in the machine's
`panicPayload`, not here** — a TCB seam the certificate must name.
BUG-004 (open: boxing identity and defined-type payloads);
latitude R9/R10 pin panic values and abort-line rendering to gc.

**C-31 · `return f()` tuple splat — S — K1** · `emit.go:2574-2591` + A-3.

**C-32 · return and named / synthetic results — M — K1** · `emit.go:2561`,
2592–2604; `$resI` synthesis 2149–2166. Result expressions evaluate
left-to-right, interface-typed slots wrap, then `return`. Bare `return` emits
empty results and the machine reads the named result locals at frame exit.
- *Notes*: the **defer/named-result read-back contract straddles the
  frontend/machine seam** — deferred functions run after the result locals are
  written and may mutate named results. The frontend's obligation is only that
  result-local naming is stable; the read-back timing is machine semantics.
  `returns/*`, `defer/defer-named-return`, `defer/defer-named-result-lifo`.

### 3.8 Assignment forms

**C-33 · multi-assign / swap / tuple assign — M — K1** · `emit.go:2819-2826`
(lhs), 2958–2985 (rhs). The wire `assign` carries lists and the **machine**
performs Go's two phases (operands left-to-right, then stores left-to-right),
which is what makes `a,b = b,a` work.
- *Spec*: spec#Assignment_statements' two-phase rule.
- *Must preserve*: the frontend must not pre-collapse the phases; its ANF
  hoists are RHS-side and order-preserving.
- *Guardrails*: `multi-assign/*` (8), `structs/tuple-field-swap`,
  `maps/tuple-*` — BUG-025, BUG-033, BUG-034, BUG-035, BUG-037.
- *Notes*: tuple-RHS with an interface-typed target owing boxing **fails
  closed** (2830–2842) — components cannot be wrapped post hoc.

**C-34 · call-RHS arity/order policy — L — K2**
- *Does*: three-way routing. Multi-value calls and all-ident-target single
  calls stay a direct call-statement assign (machine evaluates target addresses
  first). A **single-value** call onto an *addressed* target falls to the
  generic ANF path (the call runs first: `a[i] = f()` with `f` mutating `i`
  uses the NEW `i`). Builtin and conversion RHSes always take the generic path.
- *Anchor*: `emit.go:2862-2957`; ident-target scan 2873–2878; builtin guard
  2886–2892; conversion guard 2893–2905; arity comment 2916–2921;
  interface-target hoist-then-wrap 2936–2952.
- *Spec*: spec#Order_of_evaluation — latitude **E2** ("call vs. assignment-
  target operands", PINNED to gc, call-first) under reading **I-2**.
- *Must preserve*: **membership, not equality.** The shapes reproduce gc's
  observed order per arity class (`multi-assign/target-eval-before-call`,
  `multi-assign/index-target-rhs-call-order`, `multi-assign/call-write-back-order`)
  — but E2's plausible envelope is *both* orders and their interleavings. A
  certificate that pins the current order into its statement freezes a gc-pin
  as a fidelity claim. BUG-052 is the record of the machine being on the wrong
  member.
- *Notes*: the two double-emission traps (B-10) live here. ⚠ **A
  COUNTERFACTUAL, marked as one** (2026-08-21 audit-fix round): the sentence
  that used to stand here — "a multi-value call onto addressed targets cannot
  be hoisted and falls to the generic path, which refuses tuple shapes" — was
  reconstructed from the in-code comment at `emit.go:2869-2872` ("a MULTI-value
  call onto addressed targets cannot be hoisted and fails closed rather than
  silently reordering") and does **not** describe the code. The routing test at
  `:2922` is `allIdentTargets || isMultiValue`, so a multi-value call onto
  *addressed* targets takes the **call-statement path** via the `isMultiValue`
  disjunct — target addresses first, no refusal. The only tuple refusal on this
  spine is `:2830-2841`, and it fires on a different condition
  (an interface-typed target in a multi-value assignment), before the routing.
  So the comment and the code disagree, the census inherited the comment, and a
  certificate must read the routing rather than either prose.

**C-35 · compound assign `x op= e` — M — K1** · `emit.go:2717-2742`;
`emitReadWriteTarget` 3860; `containsCall` test 3861. Pure lvalues emit target
and read independently (double evaluation is claimed unobservable); an lvalue
containing a **call** pre-binds its address to a temp so the address is
evaluated once.
- *Must preserve*: the lvalue's address is computed once (spec); read before
  the op, store after; the RHS's effects come last. The purity predicate is
  `containsCall`, i.e. "call-free", **not** effect-free — a panicking pure
  operand panics identically both times, first at target-eval, and the proof
  must say why re-evaluation is unobservable.
- *Guardrails*: `structs/selector-eval-once`, `maps/compound-assign-eval-once`,
  `ints/compound-assign-wrap`, `floats/compound-assign`.

**C-36 · map compound assign / `m[k]++` — M — K1+K2** · `emit.go:3896`;
key-box comment 3909–3915; RHS-order comment 3892–3895; synthetic `1`
3928–3947; dispatch 2729–2733, 3969–3973. Base and key hoisted once each (key
boxed **before** hoist for interface keys); the synthetic `1` takes the value
type's underlying numeric kind (BUG-042). Nil-map store panics with operands
already evaluated.
- *The order half is MEMBERSHIP, not equality* (retagged K1 → K1+K2 in the
  2026-08-21 audit-fix round — this was a misclassification in the *worse*
  direction, a latitude pin sold as a forced order). "RHS emitted after base
  and key" is annotated **gc order** in the code's own comment
  (`emit.go:3892-3895`), and that is precisely latitude **E4** (targets-vs-RHS
  unordered panic order, "(b) PINNED to OUR point"; base-vs-key inside the
  target is E3's axis, whose F2 reading is UNSEQ across the target's compound
  sub-events). The frontend is the choice site — the hoist order *is* the
  realization — so a certificate must say "the emitted order is a member of
  E3/E4's envelope", never "the emitted order is the order". Observable only
  as which panic wins.

**C-37 · inc/dec — S — K1** · `emit.go:3961`; type resolution 3986–3994;
decoder fail-closed on a non-numeric carried type `NativeToIR.lean:572-576`.
`x++` ≡ `x += 1` at the operand's **underlying** kind. BUG-042 (a named wire
type defaulted the literal kind to `int` → stuck; grossmith seed 559);
`ints/defined-incdec/*` (8), `maps/incdec-value-kinds/*`.

**C-38 · chan-recv assignment — L — K1+K2**
- *Does*: a dedicated `chan-recv` statement. The machine performs the
  **communication first**, then evaluates target operands, then stores
  left-to-right. Blank `ok` drops to the 1-target form; a blank value receives
  into a fresh temp (the receive still happens). A two-target form with a
  map-element target rides the machine's `map` delivery target; a single-target
  map element uses post-statement map-assign.
- *Anchor*: `emit.go:8529`; dispatch 2775–2779; blank arms 8544–8552; map
  two-target 8554–8571; map single-target 8573–8614; refusals 8620–8623, 8564;
  `emitMapTargetWire` 8491.
- *Spec*: spec#Receive_operator + spec#Assignment_statements' two phases.
- *Must preserve — K1, the spec-FORCED conjuncts* (three, and the certificate
  states these as trace equality):
  (i) the **communication commits before target-operand evaluation** — spec's
  two phases with the receive as the RHS operand;
  (ii) **call-bearing target operands auto-hoist pre-receive** — forced,
  because spec#Order_of_evaluation puts function calls and **receive
  operations** in one lexical left-to-right order, so a call lexically left of
  the receive must run before it;
  (iii) **stores land left-to-right** after all operand evaluation, and blank
  forms equal full forms minus the store.
- *MEMBERSHIP — the K2 conjunct, stated separately because it is a different
  kind of claim* (split out in the 2026-08-21 audit-fix round; the row
  previously ran all four conjuncts together under one "must preserve", which
  invites a certificate to pin the fourth). **Conjunct (iv):** where a
  **panicking non-call** target operand's panic lands relative to the
  receive — post-receive today,
  argued in-code at `emit.go:8577-8582` — is latitude **E13** (non-call
  panicking operations vs sibling calls/receives; reading **UNSEQ**, I-2 /
  L-013). E13's own disposition is unambiguous and is quoted here so this row
  cannot regress into a pin:
  > **NO PIN MAY BE TAKEN HERE.** Deliberately **not** a corpus case, and no
  > strict-lane row may pin either axis: the machine and gc realize different
  > members on the assertion axis, so a strict pin would record a divergence as
  > a fidelity failure, and a pin on the indexing axis would freeze an
  > agreement that the spec does not require. This is a census row, nothing
  > more.
  > — `docs/2026-08-11_latitude-inventory.md:732` (E13)
  So the certificate has exactly two honest options for conjunct (iv): state it
  as **membership in E13's envelope** (any relative order of the non-call
  operand's panic and the communication, subject to the hard constraints —
  calls/receives/binary-logical lexically ordered among themselves, a call's
  arguments before it), or declare it **explicitly out of certificate scope**
  and prove only (i)–(iii). It may never be stated as equality with the
  current post-receive placement, and no guardrail row may be added to pin it.
- *Guardrails*: `channels/recv-edge/*`, `channels/recv-order/*`,
  `channels/recv-map-elem/*` — BUG-022, BUG-028, BUG-029, BUG-030, BUG-033.
  None of these pins conjunct (iv), and none may be extended to.

**C-39 · bare receive statement `<-ch` — S — K1** · `emit.go:2292-2312`.
Zero-target `chan-recv`. **BUG-024**: the expression-position hoist path left a
residual ident the decoder rejected — a whole-program error rather than
receive-and-discard, i.e. a fail-open history at the boundary.

**C-40 · map element assignment `m[k] = v` — S — K1+K2** ·
`emit.go:2783-2816`. Base → key → value order; nil-map store panics after
operand evaluation. `maps/index-assign-eval-order`,
`maps/nil-assign-eval-before-panic`.
- *The order is MEMBERSHIP, not equality* (retagged K1 → K1+K2 in the
  2026-08-21 audit-fix round, same worse-direction misclassification as C-36).
  spec#Order_of_evaluation orders only calls, method calls, receives and binary
  logical operations; `m`, `k` and `v` are none of those unless they contain
  one. Base-before-key is E3's axis (inter/intra-target operand order, PINNED
  to OUR point, **known ≠ gc** at the multi-target shape) and
  target-operands-before-RHS is E4's — both open envelopes, both realized right
  here by the emission order. What IS forced, and stays K1: the nil-map store
  panics only after every operand has been evaluated, and a call among the
  operands keeps its lexical position.

**C-41 · blank identifier — S — K1** · targets `emit.go:2996-2998`; chan-recv
8544–8552; goto-degrade 1718–1732; range vars 3598–3603; hoist collector skips
blanks 1971–1973. Blank targets evaluate their RHS or communication exactly as
non-blank, store nothing, and create no binding.
- *Notes*: **BUG-035** (a blank among the targets diverted multi-assign off the
  spine, losing phase-1 capture) and the goto blank-decl F4 both lived here.

### 3.9 Send, and the statement-position sync surface

Three rows the first pass MISSED — added by the 2026-08-21 audit-fix round
after the auditor found statement kinds and a whole lowering family with no
census entry. Their absence is itself the datum: a census is only useful if it
is total, and the gap was on the concurrency side of the statement dispatch,
which is where the census's own §0 says the unexercised-path risk lives.

**C-42 · send statement `ch <- v` — S/M — K1** · `emit.go:2412-2437`; channel
`:2421`, value `:2425`, boxing `:2429`, element type `:2433`; non-channel
operand refuses `:2419`.
- *Spec*: spec#Send_statements — "**Both the channel and the value expression
  are evaluated before communication begins.**" (verbatim, go1.26.5 pin).
- *Must preserve*: both operands are evaluated, each exactly once, **before**
  the communication begins; the value is boxed iff the element type is
  interface-typed, at the element type; the wire carries the element type so
  the machine's blocking/buffer semantics type the transfer; a send on a closed
  channel panics at communication time, i.e. after both operands are evaluated.
  Effectful operands ride A-1's hoists, so their events land in the statement
  prefix — the same order-preservation obligation as every other operand list,
  not a special one.
- ⚠ *An open census question this row surfaces, recorded not decided*
  (2026-08-21): the code emits **channel then value** and its comment
  (`emit.go:2413-2416`) cites "spec §Send statements" for that *order*. The
  spec text above orders neither against the other — it orders both against the
  communication. And spec#Order_of_evaluation's left-to-right rule is scoped to
  "the operands of an **expression, assignment, or return statement**", a list
  that does **not** name the send statement. So whether channel-before-value is
  forced, or is one more E12/E13-class frontend pin, is **not settled by the
  text**, and the corpus pins one order today
  (`channels/make-edge/ordinary-send-eval-order`, whose operands are two
  calls). This row does not rule on it: the ruling belongs to
  `docs/2026-08-11_latitude-inventory.md`, and the honest disposition is to
  census the point there before any certificate states C-42's order clause as
  equality. Until then, treat the order half as unresolved rather than K1.
- *Guardrails*: `channels/make-edge/ordinary-send-eval-order`,
  `channels/send-closed-panic`,
  `channels/deadlock/{send-full,send-nil,send-unbuffered}`,
  `goroutines/close-wake/*`, plus the select send clause's twin (C-17,
  `emit.go:8843-8865`, where the *entry-time* order channel-before-value **is**
  pinned by spec#Select_statements' step 1).

**C-43 · statement-position sync-primitive method call — M — K1** ·
dispatch `emit.go:2387-2396`; handler `emitSyncOpStmt` `:7975-8014`; op table
`syncOpFor` `:7935-7961`; `Done` → `wgAdd(-1)` `:7997-7999`
(`syncNegOne` `:7963-7965`); `Add` arity guard `:8001-8003`; refusal `:8013`;
receiver recognition `syncSelectionPrim` `:7907-7916` and address
`syncSelectionRecvAddr` `:7925-7930`. Design: `docs/2026-08-09_sync-package-design.md`
§7; decoder arity re-validation `NativeToIR.lean:683-701` + `syncPlan`.
- *Does*: `mu.Lock()` / `mu.Unlock()` / `rw.{Lock,Unlock,RLock,RUnlock}()` /
  `wg.{Add,Done,Wait}()` in statement position become a `sync-op` wire
  statement whose single argument is the primitive's **address**; direct and
  **promoted** (embedded-field) receivers both resolve, the promoted form
  walking `Selection.Index`'s prefix to the field's address.
- *Must preserve*: the op's argument is the address of the *same* cell the Go
  selection denotes, computed at the statement's position (a nil embedded
  pointer hop panics at the deref, at Go's point); `Done` is exactly
  `Add(-1)` — gc's own definition, so the lowering is a definitional unfolding
  and not an approximation; **every recognized-but-unmodeled member fails
  closed** (`TryLock`, `WaitGroup.Go`, …), never falls through to an ordinary
  call, since a `sync.Mutex` method that lowered to a plain call would run no
  synchronization at all and answer with status ok. The blocking/fatal
  semantics themselves are the machine's (latitude R8/R11), not this row's.
- *Guardrails*: `sync/mutex-{basic,double-lock,order,protected,unlock-fatal}`,
  `sync/rwmutex-*` (5), `sync/waitgroup-*` (7), `sync/promoted-mutex`,
  `sync/out-of-scope-{cond,trylock}` (the fail-closed pins),
  `sync/composite-literal`, `sync/escapes`. See C-28 for the `defer` twin and
  its recorded deferred-operand gap.

**C-44 · `once.Do(f)` — the two-function desugar — L — K1** ·
`emitOnceDo` `emit.go:8030-8093`, rationale 8016–8029; arity/signature
refusals 8031–8038; `$onceDone<N>` lift 8057–8066; `$onceDo<N>` lift
8067–8090; call site 8091–8093. Design: `docs/2026-08-09_sync-package-design.md` §3.
- *Does*: `once.Do(f)` becomes a call to a **synthetic per-site function**
  `<enclosingFunc>$onceDo<N>(&once, f)` whose body is
  `$onceStarted := onceBegin(&once); if $onceStarted { defer $onceDone<N>(&once); f() }`,
  with `$onceDone<N>` a second synthetic that runs `onceComplete`.
- *Must preserve*: (i) the receiver address and `f` are evaluated **once, at
  the call**, in that order (they are the synthetic's arguments, so this is
  C-25/B-6's machinery, not new); (ii) **completion is deferred inside the
  synthetic's own frame**, matching gc's `doSlow`, so `done` is set when `Do`
  returns and not when the *caller's* frame exits — the first inline version
  deferred to the caller and starved every later `Do` in the same function
  into the park, caught red by `sync/once-basic/runs-once`; (iii) a panicking
  `f` still completes, through the ordinary panic-path defer drain; (iv) the
  happens-before edge the doc's `Do` promises — "the return from f
  *synchronizes before* the return from any call of once.Do(f)" — is carried
  by `onceBegin`'s acquire, which is machine semantics this row must hand over
  intact rather than reproduce; (v) the two lifted names are per-site and
  qualified by the enclosing function (`liftSeq`, the BUG-027 discipline), so
  D-7's injectivity covers them.
- *Notes*: the only sync member whose lowering **synthesizes control flow**
  rather than emitting one op, which is why it is L: the obligation is a
  simulation between `sync.Once`'s documented contract and a two-frame,
  defer-bearing program shape, and three of its five conjuncts are about frames
  and scheduling rather than values. Nested `Do` parks into the deadlock gc
  realizes (`sync/once-nested-do`).
- *Guardrails*: `sync/once-basic/{runs-once,panicking-f,across-goroutines}`,
  `sync/once-nested-do`; `defer once.Do(f)` is a recorded refusal (C-28).

---

## 4. Chapter D — declarations, scoping, identity

**D-1 · `var` declaration lowering and multi-value specs — M — K1** ·
`emit.go:3054`; arity guard 3110–3118; `emitSpecDecls` 3121–3161; multi-value
reroute 3191–3244; interface-conversion refusals 3147, 3198–3221; scoping
argument 3183–3190. A spec pairing N names with **one** tuple-typed expression
(`m[k]`, `<-ch`, `x.(T)`, a multi-call) reroutes through `emitAssign` as a
synthetic `:=`; grouped decls mixing forms lower to a **sequence via the hoist
accumulator** (a wire block would mis-scope the declarations).
- *Must preserve*: each spec's initializer runs in source order; scoping is
  identical to Go — the accumulator splice is scope-preserving **because
  `emitDeclStmt` is only reachable from a statement list**, a global invariant
  the certificate must carry.
- *Guardrails*: `spec-examples-decl/var-comma-ok-matrix/*`,
  `spec-examples-decl/{index,receive}-comma-ok/*`,
  `spec-examples-decl/var-decl-forms/*` — **BUG-057** (two-variable comma-ok
  var declarations silently dropped the ok flag).

**D-2 · `const` and local `type` erasure — S — K1** · `emit.go:3058-3074`.
`const` decls are no-op statements (uses are value-folded, B-13); a local
`type` decl registers in the **global** type table and lowers to a no-op — a Go
type declaration has no runtime effect, which is why `goto` over it is legal
(`control-flow/goto-over-type-decl`).

**D-3 · block scoping by source name — M as a global invariant — K1** ·
`emit.go:2180` (`emitBlock`), 2168–2176 (`localName` + rationale). Locals keep
their **source** names; GoCore's lexical scoping distinguishes same-named
locals at execution; there is no alpha-renaming pass.
- *Must preserve*: for every emitted block shape, the wire scope structure
  matches Go's block structure exactly. **Every synthetic block in this
  inventory claims to be either a Go implicit block or a fresh invisible scope
  containing only `$`-temps** — that claim is the shared premise of A-1, C-1,
  C-5, C-11, C-14, C-20 and D-1, and it is the single most reusable lemma in
  the statement chapters.
- *Notes*: the two known places where name-only wire + declare-then-assign
  decoding breaks the model are A-9 (shadow capture) and C-20/C-22 (goto
  hoisting). Guardrails `scoping/*` (7) + 8 negatives.

**D-4 · TypeId/FuncId qualifier = the declaring package's IMPORT PATH — M — K1** ·
`identity.go:80-89`; consumers `emit.go:4579`, `identity.go:99, 110, 120`.
Go's semantic type identity is keyed on the import path (spec#Type_identity;
gc's own panic text names the class), so `Ty.eqb (.defined a) (.defined b)`
decides Go's real identity only because the frontend mints real identities.
**BUG-010**; `docs/2026-08-18_multipackage-identity.md` §1. The v1 fail-closure
`checkPackageNameCollisions` was retired as vacuous.

**D-5 · main-package, universe and stdlib names stay BARE — S — K1** ·
`identity.go:99-105`. Main-package names are the corpus subject namespace and
are dot-free, so they cannot collide with qualified keys under D-7.

**D-6 · key-grammar guard: dotted import paths REFUSE — S — K4** ·
`identity.go:128-144`; invoked `emit.go:471`. `TypeId.unqualified` strips at
the **first** `.` (the reflect-`Name()` observation contract), so a dotted path
would break injectivity. ⚠ Known rollback gap: `badKeyPaths` is not restored by
the H-11 dry run (`emit.go:801-814`) — conservative direction (a stale entry
refuses).

**D-7 · the key-grammar injectivity lemma — M — K1 (THE reusable one)** ·
`docs/2026-08-18_multipackage-identity.md` §1.
- *Statement*: Go identifiers contain neither `.` nor `/`; dotted paths are
  refused (D-6); therefore in every admitted key the first `.` of the
  bracket-free head separates qualifier from type name, and distinct
  (path, name) pairs give distinct keys. FuncIds inherit it by dot count: bare
  main name 0, qualified 1, method `<TypeId>.<method>` 2; synthetic ids use
  `$`, which identifiers cannot contain; generic stencils bracket. **No two
  constructors can emit one string.**
- *Constructor set to enumerate*: plain func (bare / qualified), method,
  `$initN` (bare / qualified), `$pkginit`, lifted `<FuncId>$litN`, generic
  stencil `<FuncId>[targs]`, promotion wrapper, interface anchor
  `<Iface>.<M>`, imported/sync stub, plus `$recv`/`$pN`/`$resN`/`$wN`/`$cN`.
- *Notes*: a genuine, self-contained string-grammar theorem. Prove it once and
  a dozen rows cite it. Backstopped mechanically by E-28's collision registry
  and `NativeToIR.lean:1395-1399`'s duplicate-FuncId sweep — but see §10 hole
  H-c: the **TypeDef** side has no decode-time sweep.

**D-8 · the rendering residue: display vs identity — L — K1 (not
frontend-fixable)** · `docs/2026-08-18_multipackage-identity.md` §3.
`TypeId.unqualified` strips before the first `.`; message renderers print
VERBATIM; gc renders panic qualifiers with the package **name**. Three path
shapes: (1) path == name → both channels exact; (2) dotted → refused; (3)
multi-segment dot-free (`red/inner`) → identity correct but a panic message
renders `red/inner.T` where gc prints `inner.T`. **BUG-059**, pinned
deliberately red by `multipkg/same-name-identity-panic`. "No single key string
can simultaneously be path-injective and byte-equal to gc's deliberately
ambiguous name-qualified message" — the structural fix separates display from
identity in GoCore. §4's raft ruling keeps raft in shape 1 via a mechanical
import rewrite — **a recorded subject delta**: the validated program is not
byte-identical to upstream raft.

**D-9 · import resolution — S — K1** · `load.go:113`, 141, 549. An import path
is local exactly when `<caseDir>/P` has non-test `.go` files; discovery is
import-driven so unnamed subdirs stay inert; escaping paths are never local.
The go-run oracle resolves identically by a different mechanism
(`tools/coverageharness`, `GO111MODULE=off`), so a disagreement is a visible
red rather than a harness invention.

**D-10 · per-unit type-check with `setUnit` — M — K1** · `load.go:571`,
597–637, 641–650; `identity.go:32`; mono crossings `mono.go:501-505, 662-666`.
Type-check order is **weaker** than init order — any dependency order will do,
and **conflating the two produced BUG-060**. Each unit has its own
`types.Info`; the invariant that makes `setUnit` correct is "AST nodes belong
to exactly one unit".

**D-11 · file presentation order = lexical filename order — S — K2** ·
`main.go:68-76`, `load.go:196-205`. The spec defers `init()` order and
multi-file declaration order to "the order in which the files are presented to
the compiler"; sorting by filename is the go command's documented behavior.
Latitude **E8** records this as a deliberate NARROWING to the go command's
realization — a conforming non-go-command build system is outside the envelope.
`init/multi-file-order`.

**D-12 · duplicate-TypeId refusal (whole program) — S — K4** ·
`emit.go:474-487`. Caught the generics G3 first cut double-emitting
`main.valueGetter[int]`.

**D-13 · function-local type declarations join the global table — S — K1** ·
`emit.go:3062-3073`, 460–466; `wire.go:106-112`. See E-29 for the generic case.

---

## 5. Chapter E — types, method sets, generics

Thirty-six rows. Ledger chapters: *Properties of types and values*, *Structs
and fields*, *Methods and method sets*, *Interfaces*, *Generics*.

### 5.1 Type lowering

**E-1 · the type choke point — M — K1** · `wire.go:344`; substitution applied
first 348–350.
- *Must preserve*: `emitType(t) = ⟦σ(t)⟧` under the active stencil environment;
  soundness of `Ty.eqb` w.r.t. Go type identity is
  `Ty.eqb ⟦t₁⟧ ⟦t₂⟧ = true ⟹ types.Identical(t₁,t₂)` on the admitted surface.
  Injectivity is not needed.
- ⚠ *The uniqueness claim is FALSE as a fact and must be carried as an
  OBLIGATION* (corrected 2026-08-21, audit-fix round). The row previously
  asserted "**`emitType` is the only producer of `Ty` nodes**" and that "every
  wire type comes from exactly one function". Measured at `4ef05649`:
  - **37 inline wire-type literals** outside `wire.go`'s `emitType` family —
    32 in `emit.go`, 3 in `fmtdesugar.go` (231, 352, 448), 2 in `mono.go`
    (521, 532). Derivation: `grep -n 'map\[string\]any{"kind":' *.go` minus
    `wire.go`'s own 20 (all inside `emitType`/`emitBasic`/`intType`/
    `floatType`/`emitInstantiatedNamed`). Most are structurally trivial
    (`{"kind":"bool"}`, `{"kind":"pointer","elem":…}` over an already-emitted
    element), which is why nobody noticed — but "trivial" is a per-site
    argument, and there are 37 of them.
  - **5 `emitBasic` bypasses** — `emit.go:3800, 3938, 3988, 6428, 6445` call
    `e.emitBasic(b)` directly, skipping `emitType`'s `applySubst` step
    (`wire.go:348-350`). Sound today only because a `*types.Basic` is
    substitution-invariant — an argument that holds for `emitBasic`'s domain
    and nowhere else. Five further sites reuse the `intType`/`floatType`
    helpers (`fmtdesugar.go:334`; `emit.go:3733, 4528, 7964, 8286`).
- *So the real statement is a CONSOLIDATION obligation*, and it comes in two
  parts: (a) discharge the 42 bypasses one by one — for each, show the literal
  equals `emitType` of the Go type it stands for under the active
  substitution; or (b) do the cheap thing first and route them through
  `emitType`/typed constructors so the uniqueness argument becomes true by
  construction, leaving a single site to reason about. (b) is a mechanical
  refactor of the kind Tier 0 (§11) collects, and it converts an argument that
  is currently 42 separate hand-waves into one lemma.
- *Notes*: substitution is the identity outside stenciling.

**E-2 · basic kinds and untyped-constant defaults — S — K1** ·
`wire.go:522-568`; `intType` 570; `floatType` 574. `byte`/`rune` are handled by
**kind**, not by `Basic.Name()`, so `byte ≡ uint8` and `rune ≡ int32` in wire
identity. The four untyped kinds fall back to their spec default types (should
be unreachable after a clean `Check` — a validator can assert that).
⚠ `Complex64`/`Complex128` are absent from `emitBasic` (fail closed at 566) but
**present** in `renderBasicArg` (`mono.go:1045-1048`): a complex type can appear
inside a mangled key but cannot be emitted as a wire type. Latitude **R1** pins
`int`/`uint` to 64 bits; `uintptr` is silently widened to 64 at
`NativeToIR.lean:62`.

**E-3 · alias transparency — S — K1** · `wire.go:359-364`; mirrored at
`mono.go:200-203`, `mono.go:915-918`, `emit.go:4620`, `emit.go:5071`.
Spec#Alias_declarations: an alias contributes nothing to type identity and no
`TypeDef` is minted under its name. **Five independent sites must agree** (the
anchor list above is five; the row said "four" — corrected 2026-08-21, and the
off-by-one is exactly the kind of miscount that made M2/R3 possible); audits M2
and R3 each record one being missed, causing mis-refusals. A sixth alias arm,
`mentionsTypeParam`'s (`mono.go:116-117`), is on the *refusal* side rather than
the identity side and is not part of the agreement obligation — but any
certificate enumerating alias handling should say so rather than omit it.
- *Notes*: `main.go:39-45` sets `GODEBUG=gotypesalias=1` **before any go/types
  use** — a global process configuration the certificate depends on (under the
  toolchain's GOPATH default, go/types aborts on generic aliases). Shared by
  `run()` and `TestMain` (audit m6 — the tests pinned the wrong config).

**E-4 · named type → `interface` vs `defined` — M — K1** · `wire.go:405-421`;
`noteInterface` registration at 407.

**E-5 · a defined type keeps identity while resolving through its underlying — M — K1** ·
`emit.go:1429-1444`. `type T int` emits `{kind:"defined", target: ⟦int⟧}`.
- *Must preserve*: (i) the assert/box dynamic type of a `T`-valued expression is
  `.defined "pkg.T"`, never `⟦U⟧`; (ii) arithmetic/comparison/conversion on `T`
  agrees with the same operation at `U` — a **per-operator** obligation across
  the whole operator surface; (iii) `T`'s method set is its declared methods
  plus promotions, never `U`'s. `ints/defined-type-ops`,
  `floats/defined-type-ops`, `complex/defined-type-ops`; BUG-004 item 2.

**E-6 · structural type lowering (pointer/slice/array/map/chan/func) — S/M — K1** ·
`wire.go:422-500`. Each a congruence; `Ty.eqb` must coincide with
`types.Identical` structurally. **Channel direction is carried and is part of
identity** (451–463). `channels/directional-types`, `channels/make-directional`.

**E-7 · ⚠⚠ function-type lowering DROPS the variadic bit — M — K1 — a
CONFIRMED live silent wrong answer** · `wire.go:483-500`;
`GoLean/GoCore/Value.lean:292-294`
(`| funcType (params results : List Ty)`). Spec#Type_identity distinguishes
`func(...int)` from `func([]int)`; the wire does not. **Contrast is
deliberate elsewhere**: `variadic` IS carried on `Func`/method-table entries
(`emit.go:1544-1550`) and on interface-method requirements (`emit.go:439-446`),
both citing pre-merge audit 2026-07-31 finding 0. **§10 hole H-d, promoted
2026-08-21 from "suspected" to CONFIRMED**: a comma-ok assert on a boxed
variadic function answers `true` where Go answers `false`, with status `ok` —
so this row is not a proof obligation but a bug with a witness, and no
certificate for it should be written before the bit is carried.

**E-8 · anonymous interface canonical rendering — M — K1** · `wire.go:465-482`;
`any` 330; duplicate `emit.go:5075-5081`. Soundness rests on Go interface
identity being **structural**: `TypeString(i₁) = TypeString(i₂) ⟺
types.Identical(i₁,i₂)` on the admitted surface — an assumption about a stdlib
printer, not a proof. `any` is deliberately excluded from `noteInterface`
(satisfied by design, ships no declaration); constraint interfaces
(`!IsMethodSet()`) refuse (477–479). Note the qualifier here is package
**name** while named-type keys are path-qualified (D-4) — a residual
inconsistency argued through per path shape at D-8.

**E-9 · anonymous struct: only `struct{}` — S — K4** · `wire.go:501-508`,
constant 326. ⚠ the *mangler* spells the same type `"struct {}"` **with a
space** (`mono.go:958-963`, reflect-probed) — two canonical spellings in two
namespaces; a certificate must not conflate them. BUG-011, BUG-019;
`structs/empty-struct-literal-at-named-type`,
`structs/empty-struct-observation`.

**E-10 · tuple types are not wire types — S — K4** · `wire.go:509-516`.
No wire `Ty` denotes a tuple; every multi-value producer lowers as a
multi-target statement. Reached only via a lowering bug (audit F-B3 improved
the message to name the *construct*, not the go/types internal).

**E-11 · type parameters outside an instantiation fail closed — S — K4** ·
`wire.go:365-370`. No emitted node's type mentions a type parameter. This is
also the per-declaration quarantine trigger for generic declarations.

**E-12 · `sync` primitive `Ty` arm — M — K1** · `wire.go:389-400`. Exactly
`Mutex`/`RWMutex`/`WaitGroup`/`Once`; `sync.Locker` routes to the ordinary
named-interface path (needed for its own boxing and for `RLocker`'s result).
`⟦sync.Mutex⟧`'s zero value is the **ready** primitive — a machine-side
obligation. Registration happens at this site so the stubs ship: an earlier
version's early return skipped it and satisfaction against `*sync.Mutex`
answered a **false "no"** with status ok (BUG-053).

**E-13 · no size / alignment / layout model — L or S depending on the spec side — K1** ·
(negative result: zero hits for `align|Sizeof|Alignof|Offsetof` outside prose;
`unsafe.*` is in no builtin table). GoCore's heap is `Loc`-keyed with
`base`/`field`/`index`, never byte-addressed.
- *Notes*: **this is the biggest structural gap between "a Go AST semantics"
  and "the GoCore semantics"**, and it is §12's fourth open question: if the
  spectec side models layout, the simulation must be stated modulo a quotient;
  if it is abstract too, the row is free. Decide before writing the first
  certificate. Ledger row *Unsafe and layout* is `deferred-unsafe`.

**E-14 · zero values are derived machine-side, not by the frontend — S here / M there — K1** ·
`emit.go:6018` (omitted struct field), 1737 (goto re-entry reset), 7590 (`new`),
602 (globals zero-seed); machine `StepFn.lean:133, 900`, `Machine.lean:122, 184,
553`. The frontend never inlines a zero — it emits a **typed** node and the
machine derives. Frontend obligation: every `default`/`var`/global node carries
`⟦declared type⟧`. The machine-side lemma (`defaultValue s ⟦T⟧` = Go's zero for
every admitted `T`: nil slice/map/chan/func/pointer/interface, zeroed
array/struct, ready sync primitive) is cited by a dozen rows — a clean
separation and an ideal single lemma.

**E-15 · expression type attachment — M — K1** · `wire.go:608-620`
(`typeOf`, with an `ObjectOf` fallback and a positional refusal); contract
stated at `emit.go:3-6`. For every emitted node `n` from AST `x`,
`n.type = ⟦σ(typeof(x))⟧` and the machine's evaluation produces a value whose
dynamic type agrees. **The type-annotation soundness obligation the whole
lowering leans on.** Substitution-aware variants: `goTypeOf` (`mono.go:80`),
`typesEntry` (`mono.go:90` — substitutes the TYPE but keeps the original
constant VALUE, see E-32).

### 5.2 Declarations, method sets, satisfaction

**E-16 · struct TypeDef: field order is declaration order — M — K1** ·
`emit.go:1365-1385`; instantiated `mono.go:508-524`.
- *Must preserve*: `fields[i] = (Field(i).Name(), ⟦Field(i).Type()⟧,
  Field(i).Anonymous())` in order. Field **access** is by name, so order matters
  only where positional construction or order-sensitive comparison does — and it
  does: struct equality short-circuits at the first differing field
  (`generics/comparable-runtime-edge/struct-skips-interface-panic` pins exactly
  that), so field order is observable through *which* uncomparable field panics.
- *Notes*: ⚠ struct **tags are dropped** — preserved through substitution
  (`mono.go:260`) but never emitted (`emit.go:1378-1379`, `mono.go:516-518`),
  though spec#Struct_types makes them part of type identity. §10 hole H-f.
  `embedded` is emitted as honest shape information only; satisfaction no longer
  needs it because promotion is flattened (E-18).

**E-17 · interface TypeDef = the FULL method set — L — K1** ·
`emit.go:396-458`; registration `wire.go:258-289`; the field comment
`wire.go:120-129`.
- *Must preserve*: for every reachable interface `I`, the wire's requirement
  list equals `I`'s complete method set (name, params, results, **variadic**),
  and `T` satisfies `I` in the machine iff `types.Implements(T, I)`.
  **Absence of a declaration must mean refusal, not vacuous satisfaction.**
- *Notes*: the field comment records the original defect verbatim —
  requirements were derived from the *dispatch* table (only called methods), so
  an interface with no call site had an empty requirement list and **every
  dynamic type vacuously satisfied it** (pre-merge audit 2026-07-31, finding 0).
  Constraint-only interfaces are skipped (1396–1398) for the same hazard class.
  Emitted to a **fixpoint** (a method signature can mention a fresh interface),
  sorted, interleaved with the mono drain. `interfaces/*` (35 rows).

**E-18 · promotion flattening plus forwarding wrappers — L — K1** ·
walkers `emit.go:4714, 4744, 4765, 4794, 5086`; wrapper pass 4811, 4905;
interface-field arm 4948–4966; address arm 4984–5005; wrapper marker 5049–5055;
sync diversion 4852–4859.
- *Must preserve*: (i) a promoted field selection with index path `[i₀..iₙ]`
  denotes the same lvalue/rvalue as Go's selection, **including that a nil
  embedded pointer hop panics at the deref, at Go's point**; (ii) the machine's
  flat method table for `T` equals `NewMethodSet(T)` ∪ `NewMethodSet(*T)` keyed
  appropriately, each promoted entry's wrapper observationally equal to the
  promoted call.
- *Notes*: receiver kind at 4837–4842 follows Go's method-set asymmetry. The
  `innerPtr && !ftIsPtr` case has **two** legal sources (a pointer wrapper
  receiver, or an embedded-pointer hop mid-chain — spec: embedding `*T`
  contributes both receiver kinds) and audit F2 records the first cut wrongly
  refusing the second, killing whole exports. Wrappers carry `"wrapper": true`
  so the machine's recover walk treats the frame as transparent, mirroring gc's
  `abi.FuncIDWrapper` (BUG-015). **A missing wrapper is not benign**:
  `emit.go:273-287` corrects an earlier claim — under D2 a missing entry makes
  `firstUnsatisfiedMethod?` answer a definite FALSE and comma-ok turns that into
  a silently wrong boolean (BUG-007 finding 5). `embedding/*` (8),
  `methods/*` (20).

**E-19 · interface-dispatch anchors — M — K1** · declared
`emit.go:1399-1426`; synthesized 293–344; recording `wire.go:291-322`.
Anchor signatures are emitted under the **call site's** substitution, not with
`curSubst` cleared (arc-final audit F5) — otherwise a generic interface used at
an enclosing type parameter refused the whole export.

**E-20 · imported concrete named types: D5 markers + exported-only stubs — M — K4** ·
registration `wire.go:411-420`; emission `emit.go:5186`, 5258, 5239.
Satisfaction answers what Go answers on the **exported** method set (unexported
methods are correctly omitted — Go's package-scoped method identity, argued at
5342–5345); a call through a stub refuses. **Skip-WHOLE semantics**: any
un-emittable signature skips the entire type (5225–5227), because a *partial*
method set is exactly what D5 exists to prevent. BUG-008 (open: imported named
types have no declaration, so comparability is unknown), BUG-009.

**E-21 · sync method-set stubs fail the EXPORT rather than skipping — S — K4** ·
`emit.go:5324`. Inverted polarity vs E-20. The stated rationale was **truthed at
the S6 audit** (5313–5323): the original reason was made false by the BUG-053
class closure in the same commit that kept it. A good instance of the
gate-honesty dimension — the policy stands; only its justification was stale.

**E-22 · method-set coverage records — M — K4** · `emit.go:501-543`,
`methodSetCoverageForKind` 574; decoder enum closed at
`NativeToIR.lean:1416-1420`. One record per method-**carrying** type;
`struct`/`defined` → `full`, D5 marker → `exported`, `sync.X` → `exported`,
interfaces/aliases → no record. Unknown kind, empty kind or nameless TypeDef
**fails the whole export**.
- *Notes*: the original inline switch had `default: full` — an unknown or absent
  kind inherited the **strongest** coverage. Unreachable at the time, but a
  future kind added without choosing its coverage would have silently inherited
  a definite-answer license. Fail-closed since the S6 audit; the decoder's
  polarity is pinned by `Tests/GoCoreEval.lean:2578+`.

### 5.3 Generics

**E-23 · THE STRATEGY: full frontend monomorphization, no dictionaries — L — K1** ·
`mono.go:1-25`; `docs/2026-08-05_generics-design.md` §2, §9.1.
- *Must preserve*: for each generic decl `D` and each reachable type-argument
  vector `τ⃗`, the stencil's body is the type-substituted source body of `D` at
  `τ⃗`; instance identity is injective on (decl, args) up to `types.Identical`;
  every use site at `τ⃗` calls exactly that stencil; the instantiation closure
  reaches a fixpoint.
- *Notes*: three facts make it sound, each cited. (i) spec#Instantiations
  **defines** instantiation as substitution. (ii) go/types' own mono check runs
  on every successful `Check`, so any package the frontend accepts is statically
  instantiable **by construction** — both differential legs refuse the same
  cycles. (iii) **Generic methods do not exist in Go by grammar** — `MethodDecl`
  has no type-parameter slot — so methods monomorphize with their receiver, and
  the one feature that breaks monomorphization elsewhere (virtual generic
  methods) is absent. gc does gcshape stenciling + dictionaries, but that is a
  code-size optimization warranted observationally identical — evidence *for*,
  not against. **Reflection is the one true dictionary-forcing feature and is
  globally refused.** `generics/*` (27 rows) + 28 negatives.

**E-24 · instantiation resolution delegated to go/types — M — K1** ·
`mono.go:328`, 346–357; `load.go:74`. The frontend re-implements **no**
inference; the concrete signature comes from `types.Instantiate` over the
*generic* signature, not from substituting `inst.Type` (which mentions enclosing
parameters in derived entries).
- *Notes*: trust is inherited from go/types, and the differential **cannot see a
  go/types inference bug** because gc uses the mirrored types2 — **shared fate**,
  recorded honestly in the design note §2d. A certificate over a spectec-derived
  typing judgement would be the first independent check of this.

**E-25 · the substitution walker — M — K1** · `mono.go:165`, 296, 102, 312.
`mentionsTypeParam` must be an **over**-approximation (its `default:` returns
true so unknown shapes refuse loudly, 154–158). Termination without a seen-set
is justified by entering Named types only through their type arguments ("a
non-generic named type cannot capture an outer parameter"). One shared
`types.Context` makes repeated instantiation pointer-shared and always
`Identical`. The `Interface` arm substitutes method signatures but refuses
embedded constraints (272–274; audit F5 relaxed a blanket refusal).

**E-26 · mangled key grammar — M — K1** · `mono.go:829`, 849, 438;
`generics-design.md` §3.2. `TypeId = qualifiedOrigin "[" args "]"`;
`FuncId = wireName "[" args "]"`; an instantiated **method** FuncId is
`recvTypeId "." name` with no separate constructor. `[` cannot occur in a Go
identifier, so no mangled key collides with a declared type's key. Note
`instTypeIdForWire` also enqueues a TypeDef while bare `instTypeId` does not —
so **a type can appear inside a key without having a declaration**.

**E-27 · type-argument rendering follows reflect/runtime spelling — M — K1** ·
`mono.go:892`, 976, 1015; header 19–25. Package-**name** qualifiers, `","` with
**no** space (unlike `TypeString`'s `", "`), canonical basic names by kind,
`"interface {}"` for `any`, `"struct {}"` for the empty struct, reflect's func
spelling. **Must preserve**: `TypeId.unqualified(key)` reproduces
`reflect.Type.Name()` and Go panic texts contain the key verbatim — an
equality-with-a-third-party-printer obligation, probe-verified rather than
proved, and **scoped to the admitted argument surface** (audit M3).
- *Notes*: a deliberate deviation from the design note's own §3.2 text (recorded
  at §10 G1) — the note said `TypeString` with a name qualifier, which is exact
  for single-argument keys but divergent on multi-argument ones. BUG-013
  (`generics/instantiated-type-assert`).

**E-28 · mangled-key collision registry and cap — S — K4** · `mono.go:808`,
734 (`monoRegistryCap = 10000`). If one key names two **non**-`Identical` types,
refuse. `Identical` types under one key are fine (`byte` and `uint8`
instantiations share a key because they **are** one Go type). The cap is also
the termination argument for `drainMono` (go/types' mono check guarantees
finite, not small).

**E-29 · function-local defined types are parameterized by the enclosing
instantiation — M — K1** · `emit.go:4590-4607`; `curTargs` `wire.go:174-178`.
gc names such a type with the enclosing instantiation's arguments
(`reflect.Name()` = `"box[int]"`). **BUG-018**: the bare key *aliased*
instantiations — wrong dynamic names at one, and *refusing legal Go* at two.
`generics/local-type-in-generic`.

**E-30 · function-local defined types as type ARGUMENTS are refused — S — K4** ·
`mono.go:907-910`. gc renders these with a compiler-internal globally-unique
suffix (`main.score·1`, probed 2026-08-05) which a source-derived key can
neither reproduce nor keep injective. **The asymmetry is the whole reason**: the
two-type case would be caught loud by E-28, but the single-type divergence would
be **silent**. `generics/local-type-argument` + `mono_test`.

**E-31 · channels are outside the mangling surface — S to state, M to close — K4** ·
`mono.go:873-891`, 968–970. Any instantiation whose type argument structurally
contains an **unnamed** channel type refuses, even when the generic performs no
channel operation; the named spelling works. Arc-final audit **F9** corrected the
rationale: the comment used to claim these "cannot reach a supported wire type
either" — true pre-channels, **false since the channels arc**. Recorded red by
`generics/chan-type-arg`; the pre-existing guardrail
`generics/type-parameter-channel-ops` instantiates at a named type and never saw
it.

**E-32 · constants do NOT re-fold at the type argument — M — K1** ·
`mono.go:84-96`; `generics-design.md` §4.1.
- *Spec*: spec#Conversions — "Converting a constant to a type parameter yields a
  non-constant value … the numeric value of `P(1.1) + 1.2` will be computed with
  the same precision as the corresponding non-constant float32 addition."
- *Must preserve*: **re-type-checking substituted source is forbidden**, because
  it would turn `T(1.25)` into a typed constant and fold at exact precision
  instead of per-op float32. This is the single subtlest constraint on the
  monomorphizer's *architecture* — it forces "substitute types, never re-check
  source". Int-domain cases cannot see it; only float/complex generic cases pin
  it (`floats/generic-type-set`, `complex/generic-type-set`).

**E-33 · joint fixpoint drain — M — K1** · `drainMono` `mono.go:710`, loop
711–726, joint-termination test 722–723; `flushFuncInsts` `:620`;
`flushTypeInsts` `:495-547`, whose `did` flag (returned at `:546`) is what
makes the termination test joint rather than per-queue. Called **three** times
in `emitProgram` — `emit.go:257`, `288`, and inside the interface fixpoint at
`411` (the row said "four" while listing three; count corrected 2026-08-21,
audit-fix round — `grep -n 'drainMono' tools/nativefrontend/*.go`). Function
stencils reach new instantiated types and type stencils reach new function
instantiations, so the fixpoint must be joint: the obligation is that
`drainMono` returns only when **both** queues are empty *and* the last
`flushTypeInsts` pass did no work, which is precisely `!did && len(funcInstQueue) == 0`.

**E-34 · instantiated type declarations and method stenciling — M — K1** ·
`mono.go:449`, 461–472 (interface carve-out), 495–547, 555; wire arm
`wire.go:586-606`. Each instantiated non-interface named type gets one TypeDef
plus **one stenciled method per declared method of the origin** — the full
method set, so satisfaction and promotion stay complete. Instantiated interfaces
route through the `seenInterfaces` pass instead (a second entry would trip
D-12).
- *Notes*: **recorded residual scope of H-3** (2026-08-19): declared methods
  quarantine per declaration, but a method **stencil** still fails the whole
  export (`mono.go:486-494`), because extending the stub to stencils needs the
  instantiation rollback to interact with a stub keeping a substituted signature
  alive. `generics/stencil-quarantine/*`.

**E-35 · imported generics are not stenciled — S — K4** · `mono.go:454-456`,
396–398 ("no AST to stencil from"). Source-package generics **do** stencil
(W1.1 loaded their ASTs).

**E-36 · mono rollback journal — M — K4** · `mono.go:736-799`; kinds 746–760.
Every registration a refused declaration made (mangled key, func stencil, type
stencil, `seenInterfaces` note, `calledIfaceMethods` record) is undone, so a
quarantined body cannot poison subjects it never touched. Queue truncation is
exact because pops happen only *between* emissions.
- *Notes*: **two rounds of scope growth**. Audit m5: without journaling, a
  refused body's surviving *type* stencil (which has no quarantine) killed the
  whole export. Delta-review **R1**: the first cut journaled only keys and
  queues — `seenInterfaces`/`calledIfaceMethods` survived rollback and the
  interface declaration pass then refused **order-sensitively**, reproduced on
  the etcd-raft `Ready() <-chan Ready` shape. Re-notes of an existing name are
  deliberately **not** journaled, so rollback never deletes an entry a
  successful declaration also owns (`wire.go:252-257`).

---

## 6. Chapter F — packages, initialization, globals

Fifteen rows. Ledger chapter: *Package initialization*, *Imports and
visibility*. Design: `docs/2026-08-05_init-design.md`,
`docs/2026-08-18_multipackage-identity.md` §5.

**F-1 · within-package variable init order = `types.Info.InitOrder` — M — K1** ·
`emit.go:1274-1293`; `init-design.md` §1. `InitOrder` **is** the type-checker's
implementation of spec#Package_initialization's stepwise rule (probe-verified
go1.26.5: dependency order with declaration-order tie-break; blank vars are
ordinary entries; one `Initializer` with multiple `Lhs` for `var a,b = f()`;
zero-valued vars are **absent** — they need allocation but no init step).
Delegation, not derivation: "a re-derivation would be a second, unaudited
implementation of a spec-mandated algorithm."

**F-2 · ⚠ hidden dependencies: a too-narrow, UNGUARDED divergence — L — K2** ·
`init-design.md` §1.1 (audit response C2); latitude **E7**.
- *Facts*: the spec says hidden data dependencies leave order unspecified;
  go/types and **gc already disagree** on this shape (`init/hidden-dep-order`:
  observations 4242 vs 4624242). Both conform.
- *Must carry*: our pinned order is **known not to contain gc's**, so
  **theorems proved over our semantics do not transfer to a gc-compiled
  execution for such a program** — and **no frontend check detects the shape**.
  A certificate must carry this as a side condition, not prove it away.
- *Guardrails*: `init/hidden-dep-order` is an EXPECTED RED (`FAIL/differential`)
  with its realized order mechanically pinned by `check-golden`, so a drift to a
  third order is caught. etcd-raft has package-level vars and is exposed in
  principle.

**F-3 · between-package order = gc's PRUNED schedule — L — K2** ·
`inittask.go:1-50` (rule + evidence), `load.go:372`, 446, 340–353.
Four steps: build the graph over source units plus the transitive closure of
non-source imports keyed by `PathToPrefix`; fixpoint the node set (a package is
a node iff it has residual init work or imports a node); walk taking the
lexicographically first **ready** node by symbol name (F-4); emit pruned source
units first, then scheduled ones in walk order.
- *Spec*: spec#Program_initialization under reading **I-4** (the algorithm binds
  only observably-initializing packages; gc's pruning is conforming, and so is
  no pruning) — backed by ledger `L-011`.
- *Notes*: pruning is safe **as node deletion** because a pruned package has no
  inittask-bearing import, so everything behind it is pruned too. Step 4 is
  faithful, not a fallback: a pruned package's initializers are exactly the ones
  gc folded into the **data section** — in place before any init code runs — and
  a pruned package can hold nothing but constants. `main` is always a node and
  always last, **checked** rather than assumed (`load.go:661-666`).
  BUG-060 (the schedule omitted imported stdlib packages).

**F-4 · the tie-break sorts by LINKER SYMBOL NAME — M — K1** ·
`inittask.go:28-35`, 61, 129; sort `load.go:386-388`. Appending `"..inittask"`
is **not** order-preserving: `"x" < "x-y"` as paths but `"x-y..inittask" <
"x..inittask"` as symbols (`'-'` 0x2d < `'.'` 0x2e). `pathToPrefix` ports
`objabi.PathToPrefix` (percent-escape bytes ≤ `' '`, `'%'`, `'"'`, ≥ 0x7F, or a
`'.'` after the last `'/'`). **"This is not decoration"** — the escaping is live
(Go 1.26 ships `crypto/internal/entropy/v1.0.0`).
`multipkg/init-order-tiebreak`.
- *Notes*: **BUG-064**, the inittask double-escape (`inittask.go:156-163`,
  `load.go:453-464`): one worklist carried both paths and prefixes and re-escaped
  every popped item, so `%`→`%25` missed a row the table has and refused every
  multi-package program whose init closure reached the crypto family. The fix
  removed the path-taking helper entirely — "outside this file every identifier
  in flight is already a PREFIX, and handing a prefix to a path-shaped function
  silently double-escapes it."

**F-5 · stdlib node facts come from a generated table — M — K4** ·
`inittask.go:63-118`, 175–191; `inittask-std.tsv` (362 rows, 293 nodes at
go1.26.5). Whether `sync/atomic` has residual init work is a **fact about
compiled objects**, unknowable syntactically, so it is read from gc's archives
(`go list -export` + `go tool nm`). Anything uncovered, or marked `?`, refuses.
**Build-conditioned and toolchain-conditioned**: build constraints decide which
imports a stdlib package declares per GOOS/GOARCH, and the table is one
toolchain's archives; both legs read the same host config so they agree by
construction, but a port or a Go-pin move re-derives the table.

**F-6 · `sourceHasInitWork` is a syntactic approximation that UNDER-prunes — M — K2** ·
`load.go:260-324`. A `func init()` with a non-empty body is work (gc drops an
empty one); a package-scope var initializer is work unless go/types assigned it
a **constant** value.
- *Direction, stated honestly*: `staticinit` folds strictly more than "is a
  constant", so the rule can call a package a node that gc pruned, **never the
  reverse**. Over-pruning would delete a real edge (unsafe); under-pruning keeps
  a spurious one, which can delay an importer past a package it should have
  beaten — a real divergence, not a safe one.
- *The five extra things `staticinit` folds, re-anchored* (2026-08-21 audit-fix
  round — the list was previously given without a source, and the in-code
  comment carries only three of the five): composite literals of static
  elements, copies from other statically initialized globals, addresses of
  globals, **conversions of constants**, and — **with the inliner on** — whole
  function calls. The three-item form is `load.go:273-276`; the five-item form
  is `docs/2026-08-18_multipackage-identity.md:255-259` and `docs/BUGS.md`
  BUG-061, and the primary source both cite is
  `deps/go/src/cmd/compile/internal/staticinit/sched.go` at the go1.26.5 pin
  (ledger **L-011**'s source list). The two items missing from the code comment
  are the two that matter most to a certificate: constant conversions are
  common, and the inliner-conditional one is what makes F-7 latitude rather
  than a bug.
- *Guardrails*: pinned RED by `multipkg/init-order-staticinit` — **BUG-061,
  open**. Measured, not assumed: a 26-flavor probe puts the residual at 11 of
  26 flavors, all one-directional — `addrglobal`, `arraylit`, `arrayofstr`,
  `bytesconv`, `callinit`, `funcvalue`, `nestedlit`, `slicelit`, `staticcopy`,
  `structlit`, `structzero` (`docs/BUGS.md` BUG-061, "Size, measured"). The
  120-seed randomized harness is at **0 mismatches and cannot see any of it** —
  every package it generates has a call-valued initializer, so it is a node
  under both rules; the bug is found by construction, not by the corpus, which
  is the honest reading of "carried by a 120-seed harness". Chosen over a deeper
  staticinit port because "the rule is legible and its failure mode is a wrong
  ORDER we can measure, whereas a half-ported staticinit's failure mode is a
  wrong order we would believe."

**F-7 · ⚠ package init order is LATITUDE, not forced — L — K2** ·
`docs/2026-08-18_multipackage-identity.md` §5; ledger `L-011`; reading **I-4**.
For `var X = f()` with `f` foldable, `go run` and `go run
-gcflags=all='-N -l'` report **opposite orders for the same source under the
same compiler**. Package initialization order therefore is not determined by
spec + program at the pruning boundary — **it depends on the optimizer.** The
corpus pins gc-at-default-flags: a deterministic gc-pin of latitude carrying a
re-envelope obligation, never a fidelity achievement. All five landed init-order
cases were checked under `-N -l`; only the call-folding flavor moves.

**F-8 · globals as driver-seeded base cells; `gid` is dense in init order — M — K1+K5** ·
`emit.go:605` (`collectGlobals` — the **single** gid source), 33–42, 1225, 1240;
`init-design.md` §2; decode bound check `NativeToIR.lean:214-219`; seeding
contract `StepFn.lean:894-905`.
- *Must preserve*: `globals` is dense, in declaration order, and `gid i` refers
  to `globals[i]` — a **correspondence** property of which the decoder checks
  only the **range** half. Blank package-level vars have no cell and no gid
  (their initializers still run).
- *Notes*: the fail-closed story was **corrected** (audit C1): the original claim
  that a dangling `globaladdr` "goes stuck at first access, never wrong" was
  FALSE — `Heap.set` materializes cells at unseeded locations, and the low base
  ids a globals-bearing program names are exactly what a fresh allocator hands
  the subject's parameter/result cells, so both a malformed wire and a
  non-seeding entry produced **silent wrong answers** (verified by wire surgery).
  The permutation case retains that hazard shape and is unchecked — see J-11.
  Three rejected alternatives are argued at §2 of the design note (frontend
  inlining; env-chain global frame; `Loc.global name`; `ExecState.globals`), each
  with the machine-side invariant it would break.

**F-9 · `$pkginit` synthesis — M — K1** · `emit.go:1254`, 1295–1311;
fabricated assignments 639–659. Body = per unit in program init order: the
unit's kept `InitOrder` assignments, then bare calls to its `$initN` in source
order. Each initializer lowers through the **ordinary** `emitAssign` machinery on
a fabricated `ast.AssignStmt` whose `Lhs` are the original declaring idents — so
hoists, boxing, multi-value calls (`var a,b = f()` is ONE multi-target statement,
per the spec's "initialized together") and blank targets are the already
validated paths. `fnHasRecv` is scanned over **every** unit's initializers before
emitting any segment (BUG-026); `liftSeq` runs through segments so
`$pkginit$litN` stays unique.

**F-10 · `init()` functions are REAL frames, not inlined — S — K1** ·
`emit.go:88-102`; naming `identity.go:118-126`. Separate functions because
`return` inside an `init` must exit that init only, `defer` must run at *its*
exit, and `recover` scopes to its frame — all free with a real frame, all wrong
under inlining. `init/init-defer-recover`, `init/init-panic`.
- *Notes*: **no per-declaration quarantine for init code** — an unsupported init
  body refuses the whole export, because init runs before every subject and a
  stubbed initializer would let every subject run against silently
  uninitialized state.

**F-11 · transitive init-quarantine closure — M — K4** · `emit.go:1119-1214`,
1103; invoked 497. If `$pkginit`'s call graph — walked transitively through
function **and method** bodies — reaches a quarantined declaration, refuse at
emit time; otherwise `$pkginit` hits the stub at runtime and poisons every
subject.
- *Notes*: deliberately over-closed in three recorded ways (delta-review M1/N3):
  a quarantined function on a never-taken branch still refuses; a func value
  merely *stored* counts as reachable; an interface anchor `I.M` expands to
  **every** emitted concrete method named `M`, whatever its receiver. M1's
  failure: the first version stored the anchor's nil body and visited no
  implementation, so an interface-dispatched initializer reaching a quarantined
  function exported cleanly and poisoned every subject at runtime. Residual
  conservatism: name-based expansion ignores receiver method sets.
  `init/quarantined-init-dep`, `init/quarantined-init-iface` (EXPECTED REDS).

**F-12 · H-11 per-declaration global quarantine and the poison — L — K4** ·
`emit.go:710-837`; must run before any body (61); poison 1225–1229; skip
1276–1283.
- *Does*: an initializer that fails to lower with an `unsupported` refusal **and**
  is effect-isolated quarantines its declared vars: the cells stay on the wire
  (typed, zero-seeded, gid-dense — never dropped), `$pkginit` skips the
  initializer, and **every** reference — read, write, address-of, qualified or
  not — refuses at the single `globalAddr` choke point, so the zero in the cell
  is unreachable rather than a silent answer.
- *Must preserve*: skipping the initializer is unobservable anywhere except the
  declared cells. Cascades correctly because the poison is armed **during** the
  pass and `InitOrder` guarantees the dependency direction.
- *Notes*: the argument was **weaker and wrong before the 2026-08-20 audit round**
  (F1/F1b). It admitted any call into a non-source package on the grounds "the
  machine does not model the body in any case", and excused panics as visible
  divergences. Both refuted by probe: `var _ = fmt.Println("x")` has an effect the
  differential compares directly *even though its body is unmodeled*; a skipped
  `[4]int(shortSlice)` turns Go's init panic into a clean machine run — **a silent
  wrong answer, not a visible one**. The current argument rests on allowlist
  purity **plus** panic-freedom.

**F-13 · `initializerEffectIsolated`: a positive allowlist, TWO properties — M — K4** ·
`emit.go:861-1079`; callee allowlist 839–859 (`pureUnmodeledCallees` = exactly
`os.Getenv`, `os.LookupEnv`).
- *Must preserve*: an admitted expression is **effect-free** (evaluating it
  changes no oracle-visible state) **and panic-free** (excluded by construction:
  array-target conversions, indexing, slicing, pointer deref, type assertion,
  division/remainder and shifts by a non-constant, interface comparison, and
  method values whose receiver evaluation can deref nil). Two *different*
  properties, both required.
- *Notes*: "KEEP THIS MINIMAL. It is not a 'functions we have not modeled yet'
  list — that was exactly the refuted reasoning." `default:` refuses, so any form
  the frontend grows later defaults to refusal. A clean, enumerable positive
  list — **ideal translation-validation material**, and the best candidate in
  chapter F for an early certificate.

**F-14 · dry-run rollback set, with three recorded gaps — S — K4** ·
`emit.go:769-814`. Rolls back `lifted`, `deferNoopEmitted`, **`tmpSeq`**,
`localTypeDefs`, `localIfaceMethods`, `namedStructTypes`, mono marks.
- *Notes*: `tmpSeq` was **missing** from the first cut (audit F2) — the dry run's
  discarded temporaries bumped the program-wide counter, so 9 otherwise-unchanged
  corpus wires came out alpha-renamed. Semantically inert, but it made the
  invariant false and golden pins compare bytes. **Known gaps, recorded not
  fixed**: `syncUsed` (`wire.go:392`), `importedNamed` (`wire.go:416`),
  `badKeyPaths` (`identity.go:83`) accumulate and are not restored —
  conservative direction, no corpus case currently reaches one.

**F-15 · pass ordering is load-bearing — M — K1 (a meta-row)**
Sixteen documented "must run before/after" pins, each with a recorded failure if
violated: `enableMaterializedAliases` before any go/types use (`main.go:48`);
shim injection before type-check (`main.go:83`, `load.go:212`); `collectGlobals`
per unit in init order before any body (`emit.go:37-42`); `registerGenericDecls`
before the H-11 dry run (44–54); the dry run before any body (56–63);
`synthesizePkgInit` after the FuncDecl loop (234–239); first `drainMono` after
`$pkginit` (249–257); promotion wrappers before the interface-anchor pass
(262–267) then a second drain (273–288); `importedTypeDecls` before the interface
pass (346–350); the E5-T harvest after it (354–358); `syncMethodStubs` before the
interface pass (382–390); the interface fixpoint interleaved with `drainMono`
(409–450); `localTypeDefs` after the last drain (460–465);
`checkKeyPathGrammar` after all keys are built (468–472); `checkInitQuarantine`
after wrappers/stubs (489–497); method-set records built last (501–543).
- *Notes*: a whole-emitter certificate must respect these; `registerGenericDecls`
  ordering was caught by `spec-examples-decl/generic-type-switch` going red, and
  audit F13 corrected the second-drain note (the old "can only make a method
  visibly MISSING" safety claim was **unsound**).

---

## 7. Chapter G — library models (fmt, the E5 shims, the E5-T model)

Thirty-five rows, all **K3**. Ledger chapter: *Standard library semantics*
(`deferred-stdlib`) — which is exactly the point: these rows have no Go AST to
simulate. The obligation is

> **REFINE(pkg.Fn, D)** — for every state and argument tuple in the modeled
> domain `D`, the lowered code's observable behavior (return values, heap
> effect, panic value and occurrence, termination) equals the **documented**
> behavior of the real `pkg.Fn`; outside `D` the frontend refuses at emit time
> or the shim panics visibly, never a silent answer.

A note on the two `E<N>` namespaces, because they collide and a certificate
that cites the wrong one is unreadable. **In frontend SOURCE**, `E1..E6` are the
gallery campaign's capability *extensions* (`docs/gallery-campaign-log/g2.md`) —
`E3` = calls in short-circuit operands, `E5` = stdlib selector-call shims,
`E5-T` = its type-shaped sibling. **In DOCS**, `E1..E13` are latitude inventory
rows. Same glyph, disjoint namespaces.

### 7.1 The fmt call desugar (emit-time, per verb)

**G-1 · the fmt surface gate — S** · `fmtdesugar.go:90-94`, gate 182–185; hook
order `emit.go:6758, 6766, 6772`. Only `Sprintf`, `Errorf`, `Fprintf` are
desugared. **`Println`/`Printf`/`Print`/`Sprint` are NOT modeled**, which is
load-bearing twice: 99 corpus `main.go` files call `fmt.Printf` purely as the
`go run` stdout convention (`main` is quarantined machine-side and the harness
never calls it), and **`fmt.Sprint` is deliberately the unlowerable-construct
witness** in the quarantine fixtures (JC-17). Modeling `Sprint` would silently
turn four quarantine rows green and stop them witnessing anything — any widening
of the table must retarget those fixtures in the same commit.

**G-2 · constant-format requirement — S** · `fmtdesugar.go:214-218`. The format
must be a compile-time string constant; the verb × kind matrix is checked at
emit time. Pinned red-by-design by `fmt/sprintf-verbs/nonconst-format`. **A
translation-validation story therefore never has to model fmt's runtime parser**
— a large simplification bought by this one refusal.

**G-3 · the format parser and its verb set — M** · `fmtdesugar.go:118-154`;
`%%` fold 133; accepted set 135; `%+v` 139–146; trailing-`%` 128–130; catch-all
148–150. Accepts exactly `%d %x %s %v %+v %q %%`.
- *Must preserve*: `concat(segs, renders) = fmt.Sprintf(f, args)` for every
  accepted format, and — the harder half — **completeness of the refusal**:
  nothing outside the set slips through. That requires enumerating fmt's grammar
  (flags `-+#0␠`, width, precision, `*`, argument indexes `[n]`, remaining verbs).
- *Explicit non-coverage*: `%X %t %c %p %e %E %f %F %g %G %T %U %b %o %w` all
  refuse, as do width, precision, and every flag except `+` immediately before
  `v`. **`%w`'s refusal happens here, and G-20's soundness depends on it.**

**G-4 · arity and spread refusals — S** · `fmtdesugar.go:224-226`, 187–189.
`len(args) == len(verbs)` or refuse (fmt's `%!(EXTRA …)` / `%!v(MISSING)` marker
family is outside `D` by construction); `Sprintf(f, args...)` refuses because
static verb × type pairing is impossible under a spread.

**G-5 · the per-site LIFT and fmt's argument-evaluation order — L** ·
`fmtdesugar.go:228-287`; lift 275–284; call node 285–286; A-normal binding
255–262. The call site becomes `<enclosingFunc>$fmtN(a0…an) string`; all
argument expressions evaluate left-to-right **at the call**, then the lifted body
runs the per-verb helpers — which is where `String()`/`Error()` execute.
- *Must preserve*: the **trace of observable effects** equals `fmt.Sprintf`'s —
  specifically all of `e0..en` evaluate, in source order, strictly before any
  `String`/`Error` body runs, and each `ei` exactly once (gc-probed as
  `E1 E2 S1 S2`, never `E1 S1 E2 S2`).
- *Guardrails*: `fmt/sprintf-verbs/eval-order` (a global-appending Stringer).
- *Notes*: the one row where the proof must reason about interleaving of
  user-visible side effects. Zero-verb formats emit **no lift at all** (269–274).

**G-6 · `%d` over integer kinds — M** · `fmtdesugar.go:531-538`; conversion
376–378. Signed → `goleanShimFmtInt(int64)`, unsigned → `…FmtUint(uint64)`;
named types included and **the Stringer check is deliberately skipped**.
Guardrail `d-enum` pins the negative claim on a `type enumT int32` *with* a
`String()` method: `%d` must print `2`, not `enum!`. The asymmetry with `%x` is
the whole content of the A-F1 regression (G-11).

**G-7 · `%s`/`%v` over strings; `%v` over ints and bools — S** ·
`fmtdesugar.go:543-557`; `…FmtBool` `stdlibshim.go:341-346`. `%s` is identity on
the byte string **including invalid UTF-8** (gc's `%s` does not validate).

**G-8 · `%x` over unsigned integer kinds — S** · `fmtdesugar.go:539-542`;
helper `stdlibshim.go:324-339`. Lowercase, no padding, `0` for zero. **Signed
`%x` is outside `D`** — gc prints `-ff` for −255 and the shim has no sign path,
so it refuses rather than approximating. `x-uint`.

**G-9 · `%q` over byte-slice kinds — M** · `fmtdesugar.go:558-561`; helpers
`stdlibshim.go:348-386`. Matches `strconv.Quote` on the ASCII subset; **outside
`D` (any byte ≥ 0x80) the shim PANICS** (`:381`).
- *Notes*: the only shim whose fail-closed boundary is a **runtime panic
  reachable from lowered code**, so a certificate must carry "all bytes < 0x80"
  as a precondition on the **value**, not on the type. `q-bytes` covers 0x00,
  `"`, `\`, `\n`, 0x7f, 0x1f, ' ', '~'; `q-bytes-empty` covers `[]byte{}` and
  nil. **Gap: no corpus row drives a byte ≥ 0x80** (§10).

**G-10 · `%+v` ≡ `%v` on the modeled matrix — M** · `fmtdesugar.go:109-112`,
139–146, 355–357, 419 (`verbLit` drops the flag). This is a **claim about gc**,
gc-probed, not derivable from our code — including that the panic render is
`%!v(PANIC=…)` and never `%!+v(…)`. For structs (where `+v` adds field names) it
would be false, which is why struct/map/slice `%v` is not in the matrix at all.
`plusv-ptr-stringer`, `plusv-nil-ptr`.

**G-11 · the stringable-verb PRECEDENCE for `v s x q` — L** ·
`fmtdesugar.go:515-529` (the hoisted switch), 500–503, 531–562 (the kind matrix,
now second); doctrine header 33–43.
- *Must preserve*: mirrors gc's `fmt/print.go` `printArg`→`handleMethods` —
  `handleMethods` is consulted for exactly `{v,s,x,X,q}` and skipped for the
  `d`-family, `T` and `p`; and `printArg`'s concrete-type fast switch never
  matches a **named** type, so a defined `uint64`/`[]byte` with a `String()`
  method always reaches `handleMethods`. The lowering must select gc's branch
  for every (verb, static type) pair.
- *REGRESSION EVIDENCE*: commit `c6886a99` (2026-08-20). Pre-fix the check lived
  *inside* the `case 's','v':` arm, so the kind matrix ran first for `x`/`q`:
  `%x` over a Stringer `uint64` rendered the hex of the **number** (`[ff]` where
  gc says `[484921]`), and `%q` over a Stringer `[]byte` quoted the **raw bytes**.
  **Both silent wrong answers reporting status `ok`.** Six guardrail rows were
  added and witnessed RED first (4 `FAIL/differential`, 2
  `FAIL/frontend-export`), then went green; baseline re-pinned 2316→2322 cases,
  2177→2183 PASS, zero other movement. **The header comment stated the rule
  backwards ("numeric verbs never consult String"), which is how it survived
  review** — the doc was the failure vector.
- *Residual*: `X` is in the doctrine set (`:35`) but absent from the code's case
  list (`:516`). Consistent only because the parser never produces `X`. A
  two-file invariant a validation harness should name. **Reconciled 2026-08-21
  (holes arc)**: gc probed at go1.26.5 — `%X` over an Error-implementing
  `uint64` prints the UPPERCASE hex of the method result (`4F4F5053`), so the
  doctrine side was right about gc; the code side is safe purely via
  `parseFmtFormat`'s verb-set refusal of `%X`. The invariant is now NAMED at
  both sites (the header's "%X AND THE TWO-SITE INVARIANT" block and a comment
  on the stringable switch's case list), each pointing at the other and at the
  render-helper third leg; admitting `%X` remains a matrix widening owing its
  own differential pins.

**G-12 · Stringer/error render over a CONCRETE static type — M** ·
`fmtdesugar.go:397-469`; promotion refusal 398–402; func-value node 445–446,
461–462. The call site passes a `func() string` **method value** captured on the
once-evaluated receiver; no interface dispatch on this path. The design choice
has two reasons and only one is semantic: fmt fidelity (at every modeled site
the static type is concrete, so the dispatch target is exactly one method) and
reachability precision (JC-16: an injected Stringer interface made the census
jump to 18 LIVE with 5 false candidates on the raft tree). **Promoted/embedded
methods refuse** (`len(index) != 1`) — a real coverage bound.

**G-13 · pointer-receiver nil flag computed at the call site — M** ·
`fmtdesugar.go:433-456`; consumption `stdlibshim.go:429-432`. Matches gc's
`catchPanic` rule: when a panic occurs during the method call **and** the
argument is a nil pointer, render `<nil>` instead of the PANIC form.
- *Must preserve*: "nil-ness computed at argument-evaluation time = nil-ness gc
  observes at render time" — true because both observe the captured *value*, not
  the variable, but not obvious and worth writing down. `plusv-nil-ptr`,
  `plusv-ptr-stringer`.

**G-14 · value-receiver method through a POINTER argument — REFUSED — S/L** ·
`fmtdesugar.go:458-460`; rationale 388–396. Capturing the method value **derefs
at argument time**; gc derefs **at render time**; the nil-pointer behaviors
differ. The boundary is stated as a value-level divergence, not a "not
implemented" — the right shape for this inventory.

**G-15 · static-INTERFACE `error` argument — M** · `fmtdesugar.go:478-498`;
helper `stdlibshim.go:440-462`. The one path with a real interface dispatch edge
(`error.Error`), deliberately accepted; the log records zero reachability cost on
the raft tree. **Non-error interface types refuse** (524–526) — a
`fmt.Stringer`-typed *variable* is not modeled, only concrete Stringers.

**G-16 · ⚠ typed-nil error boxed in a static `error` argument — RECORDED SILENT
DIVERGENCE — L to close, S to state** · `fmtdesugar.go:67-76`; mechanism
`stdlibshim.go:440-446` (the nil test is interface-nil only). A `(*T)(nil)` in an
`error` variable renders through `Error()`/the panic path; real fmt's
reflect-based nil check prints `<nil>`.
- *Notes*: **the single row in this chapter that is a silent divergence rather
  than a refusal or a panic.** It is claimed unreachable in the raft subject
  ("its live error values come from constructors") — a *subject-specific*
  argument, not a language-level one, and undetectable without reflection at a
  static interface type. **Highest-value row here for a certificate to make
  explicit**, because it cannot be caught differentially unless a corpus case
  constructs the shape. For static *pointer* types the nil check is exact (G-13).

**G-17 · nested / non-string-non-error panic propagates — S** ·
`fmtdesugar.go:73-76`; `stdlibshim.go:464-472` (re-panic at 471). Real fmt would
nest-render `%!v(PANIC=… %!v(PANIC=…))`; we fail closed. The justification
("the plainpb stubs panic with string literals") is again subject-specific.

**G-18 · THE RECOVER-FRAME SPLIT — L** · outer `goleanShimFmtRender`
`stdlibshim.go:418-424` (non-recovering) vs inner `…RenderCall` 426–438
(`defer recover`); error twins 440–452 / 454–462; rationale 388–397.
- *Does*: the inner function returns `(out, panicked)`; the outer applies the
  verb post-process (G-19) **only on the non-panicking path**.
- *Must preserve*: two conjuncts, both gc-probed. (i) **The PANIC render is never
  post-processed** — gc prints `%!x(PANIC=String method: …)` verbatim, not the hex
  of that text. (ii) **`%q`'s fail-closed non-ASCII panic must PROPAGATE.** If the
  post-process sat inside the recover frame, G-9's deliberate refusal panic would
  be recovered and re-rendered as a String-method panic — "a silent wrong answer
  replacing a refusal".
- *Notes*: **the subtlest thing in these three files, and invisible to
  value-level reasoning** — both structures produce identical output on every
  non-panicking input. It is a control-flow/effect-scope obligation about which
  panics cross which frame boundary. `x-stringer-panic`, `q-stringer-panic` (both
  added RED in `c6886a99`). Conjunct (ii) itself has **no corpus row** — argued,
  not tested (§10).

**G-19 · the injected fmt helper bundle — S/M each** · all thirteen names
reserved together at `stdlibshim.go:141-145`.
`…FmtUint` (:301) = `strconv.FormatUint(v,10)` — the LSB-first digit loop plus
reversal is where an off-by-one hides; a Lean proof wants the standard
`toDigits` induction; pinned at both extremes by `d-uint`.
`…FmtInt` (:317) uses `^uint64(v)+1` — **deliberate two's-complement negation so
`math.MinInt64` does not overflow**, and `d-int` pins exactly that.
`…FmtHex` (:324), `…FmtBool` (:341), `…FmtQuoteBytes`/`…QuoteString` (:348/:352,
panicking at 381).
`…FmtStringVerb` (:398, hex path 408–416) is the **verb post-process on a method
result**: gc hands the result to the plain-string formatter, so `%x` of a
Stringer is the hex of its *string* (`"HI!"` → `484921`) — a different function
from `…FmtHex`'s hex of a *number*, and conflating them is exactly the bug class
G-11 fixed. `…FmtError` (:440) renders a nil error as `<nil>` for `%v` and
`%!<verb>(<nil>)` otherwise. `…FmtPanicValue` (:464): `string` → itself, `error`
→ its `Error()` (invoked **outside** any recover frame), anything else →
**re-panic**.

**G-20 · `fmt.Errorf` = `errors.New(<formatted text>)` — M** ·
`fmtdesugar.go:292-318`; co-injection `stdlibshim.go:111-117`. Returns a fresh,
non-nil error whose `Error()` is the formatted text and whose `==` identity is
per-call distinct — riding entirely on G-24's identity argument.
- *Notes*: **`%w` is not modeled, and its exclusion is enforced upstream in the
  parser** (G-3). With `%w`, real `Errorf` returns a `*wrapError` with an
  `Unwrap` method, not an `errorString`, so this identity would be flatly wrong.
  **G-3 and G-20 are jointly sound and a proof must not treat them
  independently.** `errors.Is/As/Unwrap` are likewise unmodeled.
  `fmt/errorf/{fresh,text,sentinel-classify,vs-errors-new}`.

**G-21 · `fmt.Fprintf(w, …)` = `w.WriteString(…)`, `w : *strings.Builder` only — M** ·
`fmtdesugar.go:198-212` (writer type-check + **early emit**, so its hoists land
first), 319–334, 339–347. Three observables: the bytes appended, the returned
`(int, error)` = `(len(text), nil)`, and evaluation order (writer before format
arguments). The return-value equality holds **only because the Builder model
never errors and never short-writes** — so G-21 depends on G-28.
`fmt/fprintf-builder/*`.

**G-22 · `binary.LittleEndian.{Uint64,PutUint64}` var-method desugar — S** ·
`fmtdesugar.go:586-593` (table), 598–650; unmodeled-member refusal 619–623;
signature-driven lowering 640–647. A two-level `pkg.Var.Method(args)` shape whose
callee is a method on an *unexported* type. `BigEndian` and every other
`LittleEndian` member refuse by name. **File-organization trap**: this lives in
`fmtdesugar.go` despite having nothing to do with fmt.

### 7.2 The E5 direct-call shims (Go-source models, injected pre-type-check)

Scope is exactly `stdlibshim.go:100-104`: **`strings.Fields`, `strings.Join`,
`errors.New`, `bytes.Equal`**, plus G-22's two `encoding/binary` var-methods.

**G-23 · `strings.Fields` — L** · `stdlibshim.go:180-226`; design argument
161–179. A byte-scan splitter over the full Unicode `White_Space` class, widths
enumerated by UTF-8 encoding rather than rune-decoded.
- *Must preserve*: the **byte-scan ≡ rune-scan lemma** — (a) the enumerated byte
  patterns are exactly the UTF-8 encodings of `unicode.IsSpace`'s closed set;
  (b) **no pattern starts with a continuation byte**, so a pattern can never fire
  from inside a preceding valid rune; (c) on invalid UTF-8 both sides treat
  undecodable bytes as field content (RuneError is not whitespace).
- *Guardrails*: `strings/fields-conformance/*` (8, incl. `unicode-space`,
  `unicode-non-space`, `invalid-utf8`), `examples/wordfreq/*` (15, as an
  integration consumer); plus a 600k-trial shim-vs-stdlib fuzz recorded in
  `docs/gallery-campaign-log/g2.md`. The separator-width computation is
  deliberately inlined (a performance decision with a lowering-shape
  consequence).

**G-24 · `errors.New` — M** · `stdlibshim.go:259-271`; fidelity argument
228–258. Four conjuncts: (i) **identity** — each call returns a distinct value
under `==` (freshness inherited from the machine's *allocator*, not from the
shim); (ii) always non-nil; (iii) `Error()` returns the constructor string
verbatim; (iv) byte-equivalence to `go/src/errors/errors.go` modulo names.
- *Notes*: (i) is an allocator property, not a shim property, and must be stated
  as such — the counterfactual is recorded: a shim that interned by text would
  silently make every same-text comparison true, and raft branches on
  `err == errBreak`. **The one delta**: the dynamic type name is
  `*<pkg>.goleanShimErrorString`, **one such type per injected package** where
  upstream has one total. Argued unobservable because user code cannot name the
  unexported upstream type, `%T`/reflection are unmodeled, and the type component
  of `==` cannot flip an answer. **That argument depends on `%T` staying refused**
  — a second cross-file invariant between G-3 and G-24.
  `errors/new-conformance/*` (6), `errors/new-sentinel/*` (4).

**G-25 · `strings.Join` — S** · `stdlibshim.go:481-496`. Byte-identical to
upstream's `Builder`-based body (same elements, separators, order); only the
allocation shape differs, which is unobservable.
`strings/join-conformance/*` (5).

**G-26 · `bytes.Equal` — S** · `stdlibshim.go:502-517`. **nil ≡ empty** falls
out of `len(nil)==0`; pinned true by `bytes/equal-conformance/nil-empty` (3).

**G-27 · `binary.LittleEndian.Uint64` / `PutUint64` — S/M** ·
`stdlibshim.go:523-532` / 534–549. **The leading `_ = b[7]` bounds check is part
of the contract**: a short slice must panic "index out of range" at that point,
before any byte is read — and the *panic index* in the message is observable.
`PutUint64`'s sole observables are the heap write and the panic, so "writes
nothing before panicking" matters when `b` is aliased.
`binary/little-endian/*` (4, incl. `short-read` with `expected_status=panic`).

### 7.3 E5-T — the imported-model path

**G-28 · the `strings.Builder` shadow model — M per method, L for the mechanism** ·
`importedmodel.go:57-103` (the pinned source), 116–126, 136–178, 183–218;
consumers `emit.go:375`, 5209–5222. A pinned mini `package strings` is parsed,
type-checked and emitted by a **fresh emitter** through the ordinary pipeline;
its real `TypeDef strings.Builder` and method bodies are harvested under the
type's own identity, so **host code needs no rewrite**.
- *Must preserve*: per-method refinement, **plus** the merge invariants —
  FuncId/TypeId agreement across two independent emitter runs and no host state
  crossing in either direction. That second half is a distinct obligation from
  method-body fidelity, and it is why §12's first open question matters.
- *Three recorded deltas* (`importedmodel.go:36-43`): `String()` **copies** where
  upstream aliases via `unsafe` (unobservable — strings are immutable);
  `copyCheck` writes `b.addr = b` where upstream routes through `abi.NoEscape`
  (escape analysis is not modeled); upstream's `grow`/`Grow` machinery is omitted
  (append growth is the machine's, latitude R2). `hostDefNames`
  (`emit.go:363-374`) is described in-code as "a PREDICTION of the host's
  interface pass" — a fragile coupling.

**G-29 · the Builder copy-check panic — M** · `importedmodel.go:67-73`;
doctrine 31–34. `panic("strings: illegal use of non-zero Builder copied by
value")` — **upstream's exact message**; a zero Builder copy is legal. The
argument that `b.addr == b` self-pointer identity is the right test *in our
pointer semantics* is the content. `strings/builder-model/copy-panics`
(`expected_status=panic`), `copy-zero-ok`.

**G-30 · partial method set: modeled bodies vs declaration-only stubs — M** ·
`importedmodel.go:121-125`, 224–230; consumer `emit.go:5203-5222`. Exactly
`{copyCheck, String, Len, Reset, Write, WriteByte, WriteString}` get bodies;
`Cap`, `Grow`, `WriteRune` remain declaration-only stubs.
- *Must preserve*: **two** theorems, not one — (i) method-set completeness for
  satisfaction/type-assertion questions, (ii) call-site refusal for unmodeled
  members. Only (ii) would silently break `interface{ Cap() int }` assertions;
  only (i) would silently answer wrong.
- *Notes*: **`Cap` is deliberately unmodeled** because it "would expose append's
  capacity growth policy, which is allocator latitude the machine does not pin" —
  a latitude decision surfacing as a coverage decision, and the right kind of
  thing to carry into the latitude ledger.
  `interfaces/assert-imported-method-set/*` (2).

**G-31 · harvest shape assertions — M** · `importedmodel.go:202-216`, 160–174.
No plain functions, no package-level state / `$pkginit`, no `unsupported`
method, and TypeDef provenance checked (model-prefixed defs pass; a def the host
already emits — `error` — is dropped to avoid the decoder's duplicate refusal;
anything else refuses). A **wire-level well-formedness** obligation, adjacent to
but distinct from semantics.

### 7.4 Injection machinery

**G-32 · the syntactic pre-type-check injection scan — M** ·
`stdlibshim.go:561-663`. Per-file import local names, then `local.Fn(...)` and
the two-level `local.Var.Method(...)` shape.
- *Must preserve*: the scan is a **superset** of the emitter's admitted shapes —
  a false positive injects a dead function (harmless), and a false negative is
  impossible for the admitted shape because a qualified selector call must spell
  the import's local name in the same file. If a shim is ever missing, the
  emitter's type-based hook refuses per declaration rather than emitting a
  dangling name (`emit.go:7152-7160`).
- *Notes*: the default local name is the path's **last segment** (582–585); a
  package whose name diverged from its last segment would make the scan miss —
  which fails closed.

**G-33 · reserved-name collision check — S** · `stdlibshim.go:668-702`; table
138–150. Any user package-level declaration matching **any** name a needed shim
injects refuses the export loudly, before the type-checker reports a bare
redeclaration. Ranges over *all* injected names, not just the key declaration.

**G-34 · ⚠ the DOT-IMPORT hole — a pre-existing documented defect — S** ·
`stdlibshim.go:31-43`, skip 590–592. `import . "strings"; Fields(x)` never
reaches the selector quarantine: it emits a dangling plain call and the machine
answers **`stuck`** ("GoCore function not found: Fields"). Visible-red, never a
wrong answer — but a `stuck` where the fail-closed doctrine wants an explicit
boundary refusal. The recorded clean fix is to refuse on `*types.Func` callees
whose package is not the user package. **The comment previously claimed a
refusal that does not exist**; corrected 2026-08-16 by the post-autonomy audit —
the second datum, alongside G-11, that *the doc was the failure vector*.
Deliberately preserved in shape by D-5.

**G-35 · per-unit injection and FuncId minting — M** · `emit.go:7148-7161`;
`fmtdesugar.go:570-575`; widened to non-main units at `load.go:206-218`. The
shim is injected into the **calling** unit and its FuncId minted in that unit's
scope, so a multi-package program gets **one shim copy per injected package** —
which is what makes G-24's "one error type per package" delta real.
`multipkg/errors-new/*` (3). ⚠ This **contradicts** the multipackage note's §6,
which still says shims stay main-package-only; the widening happened in raft W4.0
because raft's `errors.New` sentinels live in non-main units. **The doc is stale
on this point** — worth correcting when W7 opens.

---

## 8. Chapter H — quarantine and the fail-closed contracts

Six rows, all **K4**. A quarantined declaration is not simulated; it is
*absent*. Certificates simply do not exist for it — which is exactly why the
contract has to be exact.

**H-1 · per-declaration quarantine: functions and methods differ in shape — M** ·
`emit.go:148-205`; `quarantinedMethodStub` 1473; signature refusal 1491–1510;
stencils `mono.go:620-649`.
- *Contract*: a quarantined declaration refuses when **called**, never when
  merely declared, and no other observable of the program changes. An
  unsupported plain function becomes `{name, unsupported, arity}`; an unsupported
  **method** becomes a stub carrying its **real signature** (recv/params/results/
  variadic).
- *Why the asymmetry* (argued 1451–1472): `satisfiesMethodSig` compares the full
  signature, so a guessed or truncated one would answer a satisfaction question
  **wrongly** and comma-ok turns that into a silently wrong boolean. If a
  method's signature itself does not lower, the **whole export** refuses,
  carrying both reasons.
- *Guardrails*: `methods/quarantine-{sibling,interface,embedded,pointer-receiver}/*`
  (12 rows; the four `*-call`/`dispatch-quarantined` rows are EXPECTED REDS by
  design, and the `*-satisfies`/`value-not-satisfies` rows are the fail-closed
  guards), `generics/stencil-quarantine/*`.

**H-2 · the quarantine rollback set — M** · `emit.go:160-177`. `lifted`,
`deferNoopEmitted` (BUG-031), `localTypeDefs`, `localIfaceMethods`,
`namedStructTypes`, `rollbackMono` (E-36). The obligation is that a refused
declaration leaves **no trace** — see F-14 for the dry-run twin and its three
recorded gaps.

**H-3 · imported / sync / promoted-sync stubs — M** · E-20, E-21,
`syncPromotedStub` `emit.go:4872`. Satisfaction answers what gc answers on
exported methods; unexported cross-package requirements stay machine-side
fail-closed; a call through a stub refuses visibly. BUG-009's polarity: refusing
beats a false "no".

**H-4 · H-11 global quarantine + poison — L** — see F-12/F-13.

**H-5 · init code has NO per-declaration quarantine — S** — see F-10. An
unsupported init body refuses the whole export.

**H-6 · the consolidated fail-closed register — S**
Every refusal point found while cataloguing, by file. This is the boundary a
certificate's *domain* is carved from; a certificate exists only for programs
that clear all of it.

- `wire.go` — 353–357 (Invalid / recorded `substErr`) · 365–370 (type param
  outside instantiation) · 398 (`sync.X` outside the four) · 477–479 (constraint
  interface as a value type) · 508 (anonymous non-empty struct) · 516 (tuple) ·
  518 (unknown type shape) · 566 (unknown basic kind, incl. complex) · 588
  (instantiated type still mentioning a type param) · 592 · 617 (no type for
  expression).
- `identity.go` — 134–144 (dotted import path in a key).
- `inittask.go` — 178–184 (package not in the stdlib table) · 186–189 (`?` row).
- `load.go` — 157 (import both stdlib and case-local) · 160 (dotted local path) ·
  163 (`"main"` reserved) · 166 (dot import of a local package) · 437 (import
  cycle in the schedule) · 470 (two source packages sharing one symbol prefix) ·
  555 · 581 · 635 · 658 · 665.
- `mono.go` — 170 · 197 · 273 · 284 · 292 · 331 · 334/340 · 348 · 397 · 455 ·
  468 · 558/564 · 681–683 · 814 (key collision) · 819 (registry cap) · 831 · 908
  (local type as a type argument) · 955 · 965 · 967 · 969 (outside the mangling
  surface, incl. channels) · 1052.
- `emit.go`, statements — 2557 (unknown statement kind) · 2368 (print/println in
  statement position) · 2381 (`slices.*` other than Sort) · 2465/2500
  (defer/go of a builtin) · 2538/2542/2552 (goto without a label / to a
  non-top-level label / unknown branch token; also 1633, 1959) ·
  2031/2046–2050/2077 (the goto envelope, C-21) · 1650/1666/1668/1673 (labeled
  lowering shapes) · 2722/2724 (compound-assign operator/arity) ·
  2837/3147/3219 (implicit interface conversion in multi-value assignment) ·
  2910 (self-shadowing define with a call RHS) · 3076/3115 · 3661/3680 (range
  assign targets) · 3717/3809/3818/3827 (range kinds, incl. range-over-func) ·
  4039/4044/4048/4052/4085 (type-switch shapes) · 4257/4373 (switch body,
  fallthrough in the final clause) · 8829/8838/8869/8877/8882/8885/8893 (select
  shapes) · 8564/8622 (chan-recv into interface targets) · 7668/7650 (panic
  arity / panic in value position) · 8128 (defer of a sync op with operands) ·
  2419/8437/7801 (send/receive/defer-close on a non-channel).
- `emit.go`, expressions — 2214/2240/2251 (hoist-forbidden; multi-value splat of
  a non-call) · 6536–6537 · 8458–8459 · 5511–5513 · 5796–5798/5868–5870 ·
  6028/6081/8205/8270/8300/7574 · 7555–7557 (len/cap of a panicking operand,
  A-7) · 6690 · 6848/6867/6884 · 7393–7397/7401 · 7421–7423 · 7444 ·
  7464/5498/5568 · 5541/5597/5606/5611 · 5616 · 4464/4473 · 7652 ·
  5431/7327/5937/8013/8002/8032/8037 (the sync surface) · 4487/4490 ·
  5884/5891/5982/6057/6151/6099 · 5805/5841 ·
  4728/4732/4769/4772/5098/5102/5112/5124 · 5400/5410 · 6434/6466 ·
  6483–6486/6624 · 4512 (the expression catch-all).
- `emit.go`, program level — 482 (duplicate TypeId) · 519/576/591 (method-set
  classifier) · 629 · 761/1286 · 826 (non-isolatable failing initializer) ·
  1187/1194 (init reaches a quarantined declaration) · 1227 (the H-11 poison) ·
  1476/1480/1489/1495 · 1565 (method on an anonymous type) · 1572 (bodyless
  function) · 3022/3036/3044/5697/5709/5717/5829/6399/7277 (package-level
  variable with no seeded cell — 7 reference shapes) · 7301/7257 · 5225–5227
  (imported-type skip-whole).
- `main.go`, `stdlibshim.go` — `main.go:63` (more than one package in `--dir`) ·
  `stdlibshim.go:683/690/695` (reserved-name collisions).
- `fmtdesugar.go` — 148–150 (verb outside the set) · 187–189 (spread) ·
  205 (writer not `*strings.Builder`) · 214–218 (non-constant format) ·
  224–226 (arity) · 298–302/634–639 (shim not injected) · 399–402 (promoted
  Stringer) · 409–412 (unnameable receiver) · 458–460 (value receiver through a
  pointer) · 619–623 (unmodeled var-method member) · 524–526 (non-error
  interface).

---

## 9. Chapter J — the decode half: what stage 2 ASSUMES of the wire

All **K5**. Every assumption the decoder does not *check* is an unguarded
emitter obligation. Two headline findings frame the chapter.

**Unknown node KINDS: fail-closed, uniformly — PASS.** Every tag-dispatching
`match` in `NativeToIR.lean` ends in an explicit
`| other => fail s!"unsupported …"`: `decodeTy` kind `:118`, int-kind name `:63`,
float kind `:79`, chan dir `:92`, sync kind `:107`, `decodeExpr` `:320`,
`decodeBinary` `:347`, unary `:297`, `decodeCompound` `:371`, `decodeTarget`
`:403`, `decodeStmt` `:845`, sync-op `:702`, select clause `:733`, labeled body
`:844`, `decodeRange` `:998`, `decodeTypeDef` `:1263`, methodSet coverage enum
`:1419`. **No `| _ =>` turns an unknown tag into anything but an error**, there
is no `panic!`/`unreachable`, and every `Array.get!` is guarded by a preceding
size test. *The hole is not unknown tags — it is unknown or missing KEYS.*

**Unknown/EXTRA keys: NOT checked at all — fail-OPEN.**
`StrictJson.requireExactKeys` exists (`StrictJson.lean:15-19`) and is used 19×
in `CLI.lean`'s state decoder, and **zero times** in `NativeToIR.lean`. Every
wire object is read key-by-key; unrecognized keys are silently ignored
(demonstrated live: the emitter writes `"package"` at `emit.go:547` — anchor
corrected 2026-08-21; `:550` is the `"methods"` key — and the
decoder never reads it). Consequence: **a dropped optional key is
indistinguishable from a deliberately absent one**, which makes every row in
§9.2 reachable. Note what the existing primitive can and cannot do, because
§11's Tier-0 recommendation turns on it: `requireExactKeys` tests **set
equality** against one literal key list (`exactKeys` = `size == length &&
all contains`, `StrictJson.lean:12-13`), so it is exactly right for a node
shape with no optional keys and unusable for one with them — see §11.

**Round-trip / schema agreement: essentially none.** The only format agreement
is the literal string `"golean-native-v1"` (`emit.go:546` vs
`NativeToIR.lean:1356`). No version negotiation, no shared schema, no
decoder→encoder round-trip. Partial pins that do exist: `scripts/check-golden`
re-emits 7 pinned programs and diffs the decoded `repr` against
`baselines/golden/*.repr` (real emitter↔decoder drift detection, for those
programs); `scripts/check-imported-pins` does the same for 11 imported-goose R2
pins; three negative decode unit tests at `Tests/GoCoreEval.lean:2564-2579`.
Everything else rests on the differential, which exercises only wires the
emitter actually produces — structurally blind to "the emitter *could* produce
X".

### 9.1 Silent coercion and silent defaulting — the dangerous class

**J-1 · ⚠ integer-literal kind defaults to `int` — M** ·
`NativeToIR.lean:137-139` (`| _ => .int`), consumed `:155`.
`intKindOfOptType` maps **both** "no `type` key" and "type present but not
`Ty.int`" to `IntKind.int`. Obligation: every `{"expr":"int"}` carries a `type`
decoding to `Ty.int k` with `k` the literal's underlying integer kind.
**SILENT COERCION** — a `uint8` literal arriving typeless becomes 64-bit and
arithmetic wraps at the wrong width. This is BUG-042/BUG-043's defect class,
already fixed with explicit fail-closed arms for `incdec` (`:572-576`) and
range-over-int (`:910-918`) — **`Expr.intLit` still has the default**, and it is
reachable (`emit.go:6439` attaches `"type"` only if the underlying is a basic
integer; `emit.go:3727` emits a typeless int node unconditionally). §10 hole H-b.

**J-2 · blank/discard temp type defaults to `int` — S** ·
`NativeToIR.lean:1039`, `:1066`; feeders `:1032`, `:1057`.
`resultTypes[i]?.getD .int` types a `_`-target discard local as `int` when
`resultTypes` is absent or short. Bounded today because the mistyped cell is a
discard by construction; a wrong-answer hole the moment anything reads a
`$cr`/`$cv` temp.

**J-3 · `exprTypeOf` defaults an untyped node to `Ty.int .int` — M** ·
`NativeToIR.lean:430-434`. Call sites: discard locals `:1106`, `:1115`, and —
consequentially — **the range collection temp `$rcoll`** (`:880`, `:897`). For
`$rcoll` this is not a discard: a slice range whose collection node lacked
`type` would declare `$rcoll : int` and then run `.length`/`.indexGet` on it.

**J-4 · `targetBaseExpr` fabricates `$lit` / `$maplit` — S** ·
`NativeToIR.lean:409-412` (used `:799`), twin `:808-811` (used `:821`). If a
`slice-lit`/`map-lit` target is not a plain local, the element-store base
silently becomes an undeclared `.var "$lit"`. Deferred fail-closed (a stuck at
`StepFn.lean:284-286`) — **but the `makeSlice`/`makeMap` half already executed
and wrote through the real target.** Should be a decode-time `fail`.

**J-5 · `optString` silently drops a malformed range-variable name — S** ·
`NativeToIR.lean:424-427`; consumed `:856-857`; effects `:886-888`, `:948-950`,
`:952-960`, `:984-991`. A present-but-non-string `keyVar`/`valVar` becomes
"no iteration variable" and the binding statement pair is dropped — a silent
change to the **shape** of the emitted loop.

**J-6 · `targetIsBlank` returns `false` for any malformed target — S** ·
`NativeToIR.lean:418-421`. Routes to `decodeTarget`, which fails closed on the
same malformation — low risk, catalogued because it is a `| _ => false` on a
*classification* predicate.

**J-7 · `idxKind`'s dead `| _ => .int` — S** · `NativeToIR.lean:919`.
Provably dead (`idxTy` is `.int _` by the fail-closed construction three lines
above) — but it is the **exact syntactic shape of J-1's bug sitting next to the
code that fixed it**. A future edit to `:910-918` re-arms it.

**J-8 · `uintptr` widened to 64, `byte`→`uint8`, `rune`→`int32` — S** ·
`NativeToIR.lean:62`. `byte`/`rune` are spec-mandated aliases and correct;
**`uintptr` is a gc-pin of latitude R1** — record it there rather than "fix" it.

**J-9 · five silent-drop `| none => pure ()` sites in index-guarded loops — S** ·
`:734` (a **select clause** dropped), `:800`, `:821`, `:1011` (a **return result
assignment** dropped), `:1148`. All currently dead (indices are drawn from
`[:arr.size]`), but the failure mode is a silent drop, not an error: a dropped
select clause changes the nondeterminism envelope; a dropped return assignment
leaves a result local at its zero. `:1011`'s guard is the *separate*
`rs.size == results.size` test at `:1004` — one edit from live.

### 9.2 Optional-key presence tests (absence = a DIFFERENT, well-formed program)

The largest class, and unguarded because of the fail-open key check. Each row is
an emitter obligation of the form "key `K` is emitted iff the Go construct has
feature `F`". None fails closed.

| # | key / site | anchor | absence means | risk |
|---|---|---|---|---|
| J-10 | `for`.`cond` | `:1165-1167` | `.boolLit true` — **an infinite loop** | **worst in the table** |
| J-11 | `for`.`condPre` | `:1175-1179` | no hoisted cond temps | cond reads stale/unbound temps |
| J-12 | `for`.`post` / `for`.`init` | `:1169-1171`, `:1203-1205` | empty | S |
| J-13 | `if`.`else` / `if`.`init` | `:1154-1156`, `:1158-1161` | empty / no init block | S |
| J-14 | `make-slice`.`cap` | `:641-643` | `cap == len` | changes `cap()` and append aliasing |
| J-15 | `make-chan`.`cap` | `:655-657` | **unbuffered** | buffered↔unbuffered is a blocking-semantics change |
| J-16 | `slice`.`max` | `:262-264` | 2-index slice | changes the result cap |
| J-17 | `select`.`default` | `:735-737` | **blocking** select | non-blocking↔blocking |
| J-18 | `panic`.`wrap` | `:513-517` | payload already an interface | changes `recover()`'s dynamic type |
| J-19 | `panic`.`runtimeError` | `:506-508` | `false` | partially closed (a *present* flag decodes strictly, audit F7) |
| J-20 | `type-assert`.`source` | `:315-317` | no static source type | observable in the abort line (B-43) |
| J-21 | `range`.`arrType` / `range`.`len` | `:925-930` | not an array-pointer range / dynamic len | changes whether the element read derefs (C-8) |
| J-22 | expr-stmt `.resultTypes` | `:600-609` | targetless call | **deliberately** fail-open-to-old-lowering; a value-returning callee then goes stuck |
| J-23 | `var`.`init` | `:1146-1148` | zero value | S |
| J-24 | expr `.type` (`optType`) | `:132-135` | `none` | feeds J-1/J-3; **float and incdec fail closed** (`:167`, `:575`), int and nil do not |
| J-25 | `func`/`method`.`unsupported` | `:1275`, `:1321` | a real declaration | a dropped marker makes a quarantined decl look real |
| J-26 | `method`.`interface` / `.wrapper` | `:1332-1334`, `:1315-1317` | `false` | strict when present (delta-review R2); E-18's recover transparency rides `wrapper` |
| J-27 | `program`.`globals` | `:1362-1364` | zero globals — and `nGlobals = 0` disarms J-28's bound check into "reject every `globaladdr`" | fails **safe** (over-rejects) |

### 9.3 Structural, arity and ordering assumptions

**J-28 · ⚠ `globaladdr` gid ↔ `globals` index ↔ `Loc.base ⟨gid⟩` — M** ·
`NativeToIR.lean:214-219`; reader context `:1379-1381`; seeding
`StepFn.lean:894-905`; emitter source `emit.go:605`. The **range** half is
checked loudly; the **correspondence** half (dense, declaration-ordered,
`gid i` ↔ `globals[i]`) is not — **a permuted globals array is a silent
wrong-variable read/write**, retaining exactly the hazard shape F-8's docstring
describes. **The cleanest translation-validation lemma to state first**:
`collectGlobals` is documented as the sole gid source and half the property is
already discharged at the boundary.

**J-29 · positional call-argument ↔ parameter correspondence — L** ·
`:615/617/1046` (by name), `:626/627/1073` (by value); params `:1293`. The
decoder never sees the callee's signature. Arity mismatch is deferred-closed
(stuck at bind/frame exit); **type mismatch is not caught at all** — this needs a
wire-level typing judgement, which is exactly what a spectec-derived type system
could supply.

**J-30 · assignment result count vs callee results — M** · `:1035-1046`,
`:1062-1073`; deferred-closed at frame exit (`:589-592`).

**J-31 · `return` arity IS checked; per-index correspondence is not — S** ·
`:1000-1014` (fails at `:1014`).

**J-32 · `assignMany` positional lhs↔rhs — S** · `:1093-1094` (arity checked),
`:1124-1136`.

**J-33 · ⚠ `slice-lit` / `array-lit` element indices are unbounded against
`length` — S** · `:788` (`length` as `Nat`), `:797` (`index` as a **signed**
`Int`), `:799`; array twin `:277`, `:282`, `:285`. Nothing checks
`0 ≤ index < length`. **This one produces a SPURIOUS GO PANIC, not a stuck** —
an out-of-range index reaches the machine's index-out-of-range path and the
differential sees a runtime panic the real program never had. §10 hole H-c.

**J-34 · `Ty.array len` vs `arrayLit length` agreement — S** · `:83` vs `:277`;
never cross-checked.

**J-35 · `struct-lit` args are positional against the TypeDef's field order — M** ·
`:272-275`; field order `:1239-1240`, `decodeFieldDef` `:1211`. Arity/order
mismatch is a silent field shift. Pairs with E-16.

**J-36 · method receiver is prepended; `params` must NOT include it — S** ·
`:1324`, `:1342`, `:1346`.

**J-37 · ⚠ `MethodInfo.recv` vs the `recvType` string are never cross-checked — M** ·
`:1303`, `:1304`, `:1310-1311`. The dispatch **key** is built from `recvType`
while dispatch **matching** uses `recv.typ` — two independent wire fields, and a
mismatch **silently mis-routes dynamic dispatch**.

**J-38 · ⚠⚠ declaration-before-RHS ordering: the shadow-capture obligation — L** ·
decoder `:1129-1136` (also `:1044`, `:1121`, `:1132`); emitter compensation
`emit.go:2606-2630` + the fail-closed arm `emit.go:2910`. The decoder emits
`.initialization` for all declared targets **before** the assignment, so for
`x := x + 1` the RHS `.var x` would resolve to the fresh zero cell. **The
emitter's `containsVarUse` pre-bind is the only thing preventing it, and the
decoder has no idea the hazard exists.** Pure silent wrong answer if the pass
ever misses a shape; historically found by a guardrail case, not by any gate.
See A-9. **The single most proof-worthy row in this chapter.**

**J-39 · select clause ORDER is preserved into `.selectStmt` — M — K5+K2m** ·
`:711-738`. No check is possible; flagged because it is a
**nondeterminism-envelope** correspondence — the class with no differential
oracle (latitude C6/C7). *Kind corrected 2026-08-21 (audit-fix round)*: this
row was listed in the K2 register, but §0.2 defines K2 as latitude where **the
frontend is the choice site**, and here it is not — the commit choice belongs
to the machine. The frontend/decoder obligation is the dual one (**K2m**):
hand the machine the clause list in source order and unabridged, so its
envelope is neither reordered nor narrowed. J-9's dropped-clause hazard
(`:734`, a silent `| none => pure ()`) is the concrete way this can fail.

**J-40 · synthetic-name namespace disjointness — M** — see A-10.

**J-41 · `$interface-method-unreachable` is an unowned reserved FuncId — S** ·
`:1339-1341`; the duplicate sweep at `:1395-1399` catches two such names, not
one. A wire defining it converts a deliberate stuck into a silent call.

### 9.4 Identity and collision

**J-42 · ⚠ `program.types` has NO duplicate-TypeId check at decode — S to fix** ·
`:1382-1385`. `funcs` are dup-checked (`:1395-1399`), `methodSets` are
(`:1424-1428`), `globals` are (`:1374-1378`) — **`typeDefs` are not.** The
check exists emitter-side only (D-12). The `:1391-1394` docstring states the
hazard for FuncIds verbatim ("duplicate FuncIds would make `findFunctionIn?`
silently run the FIRST body for BOTH callers"); the same argument applies to
TypeDefs with no net. Also: the decoder unconditionally prepends a synthetic
`struct{}` TypeDef at `:1385`, so a wire-declared `struct{}` silently shadows or
is shadowed — while the `methodSets` path *does* refuse a wire-declared
`struct{}` record (`:1422-1428`). **The two synthesized-entry paths are
inconsistent with each other.** §10 hole H-c.

**J-43 · method FuncId is a string concatenation with a reserved separator — M** ·
`:1310` (`s!"{recvType}.{name}"`). The decoder concatenates blindly; only an
exact duplicate is caught. Injectivity is enforced **emitter-side only** by D-6.
Prove D-7 and this row is discharged.

**J-44 · TypeDef ↔ methodSet record coverage is not cross-checked — S** ·
`:1408-1428`. A *missing* record makes satisfaction refuse `unsupported` — the
correct polarity, pinned by a unit test. A *spurious* record for an undeclared
type is silently inert.

**J-45 · `"named"` vs `"interface"` type-kind tags must agree with the
declaration — M** · `:108-111`. `decodeTy` produces `.defined` or `.interface`
from the **use site's** tag, independently of what `program.types` declares.
Disagreement mis-routes boxing, asserts and satisfaction.

### 9.5 Free lemmas — invariants the decoder already discharges

Worth listing so a certificate does not re-derive them:
schema tag `:1355-1357` · `globaladdr` gid range `:214-219` · duplicate global
name `:1374-1378` · duplicate FuncId `:1395-1399` · duplicate methodSet record
`:1424-1428` · `methodSets` required `:1408-1409` · coverage enum closed
`:1416-1420` · **`variadic` REQUIRED** on funcs `:1292`, methods `:1307` and
interface method sigs `:1227` (the audit-finding-0 fix — a missing marker would
have defaulted a variadic requirement to non-variadic) · string-literal bytes
are `Nat < 256` `:179-182` · integer literal parses as `Int` `:154-156` ·
float literal `num`/`den` parse, `den ≠ 0`, and the carried type **is** a float
kind — missing and non-float both `fail` `:162-172` (exemplary) · `incdec`
carried type numeric `:572-576` (BUG-042) · range-over-int `operandType` present
and integral `:910-918` (BUG-043) · `==`/`!=` require `operandType` `:322-326` ·
`builtin-len`/`cap` require `operandType` `:246-251` · `labeled` only over
`for`/`range`/`breakable` `:840-844` (the machine's `contHeadLabel` placement
invariant, C-23) · a call in expression position is refused `:319` · an
expression statement must be a call `:628` · non-assignable lvalue `:351-354` ·
chan-recv / select-recv target count ≤ 2 `:666-667`, `:726-727` · sync-op arity
`:683-701`, **re-validated by `syncPlan`** (fail closed twice — the model row).

### 9.6 Deferred fail-closed (stuck at run time, not an error at decode)

Not silent-wrong, but they weaken "the decoder rejects malformed wire" to "the
machine gets stuck later, if reached": `Assignee.unsupported "blank assignment
target"` reaching a non-comma-ok position (`:390` + ~11 consumers) ·
`Assignee.mapElem` outside the chan-recv delivery plan (`:394-402`, deliberate) ·
a quarantined-function stub hard-coding `results := #[]` regardless of the real
signature (`:1285`) · J-4's `$lit`/`$maplit` · J-22's targetless call · J-41.

---

## 10. Holes found while cataloguing

Six things the census turned up that are **not** in `docs/BUGS.md`, the ledgers
or the corpus. Each is exactly the class the audit doctrine says green gates
structurally cannot see, which is the point of writing the census at all.

**Status after the 2026-08-21 audit-fix round.** The first pass recorded all
six as "leads, not confirmed defects — none was reduced to a witness program".
That is no longer true of two of them: the pre-merge auditor reduced H-a and
H-d to witnesses and this round re-ran them end to end. **Both are LIVE SILENT
WRONG ANSWERS with status `ok`.** The table is the follow-on holes arc's
charter input. The probes live in the auditor's scratch (`.tmp/audit/`,
untracked), so each row below restates its witness — H-d's source verbatim,
the others in enough detail to retype — and nothing here depends on a file
that is not in the repo.

| hole | verdict | witness / why not | owed |
|---|---|---|---|
| **H-a** slice default-high double emission | **FIXED 2026-08-21 (holes arc, BUG-066)** — was: verified live silent wrong answer, status `ok` | gc 1 call, machine 2, on both a slice base and a pointer-to-array base; explicit-high control agrees at 1 | ~~BUG entry + corpus row + fix~~ all landed; see B-18 |
| **H-b** `Expr.intLit`'s `\| _ => .int` | **not probed this round** — reachability argument (J-1) unchallenged, no witness constructed | reachability is by code reading (`emit.go:6439`, `:3727`), not execution | reduce to a witness, then fix (Tier 0) |
| **H-c** two missing decoder checks | **not a defect — a proposal**, restated as such | duplicate-TypeId sweep (J-42) and literal index bounds (J-33); J-33's *spurious panic* direction re-read and stands | land both (Tier 0) |
| **H-d** wire func types drop the variadic bit | **VERIFIED — live silent wrong answer, status `ok`**; the first pass's "not confirmed observable" is **REFUTED** | comma-ok assert on a boxed variadic func: gc `false true`, machine `true true` — no reflection needed | BUG entry + corpus row + `Ty` carries variadic |
| **H-e** composite-literal element order | **probed — NOT a divergence on the probed shape**; remains an uncensused latitude point | gc runs the sibling call before the non-call element's panic, the same member the ANF hoist realizes (machine 1 = gc 1) | census E12's follow-on, then a membership statement (B-19) |
| **H-f** struct tags dropped | **not probed** — genuine identity collapse in `Ty`, observability open | unlike H-d, the plausible witnesses go through reflection (globally refused) or anonymous non-empty structs (refused, `wire.go:508`) | try to construct a witness; if none exists, record as an argued-unobservable narrowing rather than leaving it a lead |

**Both confirmed holes PREDATE this branch** — they were found *by* the census,
not introduced by it: H-a's second emission dates to `a18ebd24` (2026-07-18,
"Native frontend: make (slice/map) and slice expressions"), H-d's
variadic-dropping `funcType` to `7ce738bc` (2026-07-25, "W5 slice 1b: frontend
lambda lifting"). Neither has a BUG id yet; **both owe one, and the follow-on
holes arc heads with them** — they are the two rows in this file that are
demonstrated wrong answers rather than proof obligations, so they outrank every
certificate in §11.

- **H-a · slice-expression default-high emits the base TWICE — FIXED
  2026-08-21 (holes arc, BUG-066; anchors below describe the PRE-FIX code).**
  Was `emit.go:4521/4523` (base or its address) and `:4541` (a second
  `emitExpr` of the same operand, inside the `builtin-len` for the elided
  high). Each `emitExpr` of a call hoists a **fresh** temp, so the base ran
  twice. Every other documented eval-once hazard in the file is guarded
  (`emitReadWriteTarget` 3860; BUG-047's conversion guard 2893–2905); this one
  was unguarded and unpinned. Closest relative: BUG-047, same
  silent-divergence shape. Fix + guardrails: B-18's updated row.
  - *Witness (verified end to end, this round).* Two forms, both reproducing:
    a **slice base**, `s := expensive()[:]` with `expensive` incrementing a
    counter, and a **pointer-returning array base**, `s := pf().arr[2:]` with
    `pf` returning `*box`. The emitted wire for each contains **two** call
    statements — `$c1 := expensive(); $c2 := expensive();` — with `$c1` as the
    slice base and `$c2` as the `builtin-len` operand. `go run`: **1**.
    `golean native-json-run`: `{"status":"ok","values":[{"tag":"int",
    "value":2}]}` — **2**. Control: the explicit-high form
    `expensive()[0:3]` emits one call and both sides answer 1.
  - *Example corrected*: the first pass wrote the second form as `f().arr[2:]`
    with `f` returning a **value**. That is not legal Go — slicing an array
    requires an addressable operand, and a call result is not addressable — so
    the pointer-returning `pf().arr[2:]` is the form that actually witnesses
    the hole (auditor's probe; re-verified here).
- **H-b · `Expr.intLit`'s `| _ => .int` default** (J-1). A silent coercion
  whose two siblings (`incdec`, range-over-int) are already fail-closed for
  exactly this reason. Likely a small **bug fix before a proof**, not a proof
  obligation. **Not probed this round**: the reachability claim rests on code
  reading (`emit.go:6439` attaches `"type"` only when the underlying is a basic
  integer; `emit.go:3727` emits a typeless int node unconditionally), and it is
  unchallenged but unwitnessed — say "unwitnessed", not "live", until someone
  runs it.
- **H-c · two two-line decoder checks that would convert unchecked obligations
  into free lemmas**: a duplicate-TypeId sweep (J-42) and a
  `0 ≤ index < length` bound on literal element indices (J-33, which produces a
  *spurious panic*, not a stuck). Doing these first shrinks the certificate's
  surface.
- **H-d · wire func types drop the VARIADIC bit — CONFIRMED LIVE SILENT WRONG
  ANSWER, status `ok`** (E-7). `wire.go:483-500` lowers `func(...int) int` and
  `func([]int) int` to the same `funcType [[]int] [int]`, while `Func` and
  interface-requirement entries **do** carry `variadic` (`emit.go:1544-1550`,
  `:439-446`), both citing the pre-merge audit finding that says the
  distinction matters. Spec#Type_identity makes them different types.
  - *Witness (auditor's probe, re-verified end to end this round).*
    ```go
    func variadic(xs ...int) int { return len(xs) }
    func probeAssert() (bool, bool) {
        var i any = variadic
        _, okSlice := i.(func([]int) int)   // Go: FALSE
        _, okVar   := i.(func(...int) int)  // Go: TRUE
        return okSlice, okVar
    }
    ```
    `go run`: **`false true`**. `golean native-json-run --function
    probeAssert`: **`{"status":"ok","values":[{"tag":"bool","value":true},
    {"tag":"bool","value":true}]}`** — `okSlice` is wrong, and the run is
    `ok`: no refusal, no panic, nothing red anywhere. The wire shows *why* it
    cannot be otherwise: the two `type-assert` statements carry **byte-identical
    `targetType`** (`{"kind":"func","params":[{"kind":"slice","elem":int}],
    "results":[int]}`), and the boxed value's `dynamic` is that same node, so
    the machine has no information left to tell the two assertions apart. It
    answers the same for both; Go answers differently; therefore one of them is
    wrong for *any* semantics the machine could give the node.
  - *The first pass's "not confirmed observable in the current refusal envelope
    (reflection is globally refused)" is REFUTED*: comma-ok type assertion at a
    func type is enough, and it is ordinary supported Go. **No BUG entry, no
    ledger row, no corpus case** — all three owed. The fix is `Ty.funcType`
    carrying the bit, plus the decoder requiring it (the same shape as the
    `variadic`-REQUIRED discipline §9.5 already records for funcs, methods and
    interface method signatures).
- **H-e · composite-literal element order vs a sibling call's panic** (B-19) —
  **probed; not a divergence on the probed shape.** `containsCall` is the
  effectfulness oracle, so a non-call *panicking* element is not hoisted and its
  panic can land out of source order against a hoisted sibling.
  - *Witness attempt*: `S{A: arr[i], B: f()}` with `i` out of range and `f`
    bumping a counter, the counter read from a `recover`. `go run`: **1** — gc
    ran `f()` **before** the index panic. Machine: **1**. Both realize
    call-first; the hoist agrees with gc here.
  - So this is a **latitude-census gap, not a bug** — and a gap on a point the
    spec states *explicitly*, not one it merely omits: spec#Order_of_evaluation's
    example block says `x := []int{a, f()}` "may be [1, 2] or [2, 2]:
    evaluation order between a and f() is not specified", with sibling lines
    for duplicate map keys and map-literal key-vs-value. E12's census follow-on
    lists all three as **not yet censused**, and the probe shows only that our
    member and gc's coincide on one shape — exactly the lower-bound reading the
    doctrine allows and no more. It must be censused before B-19's certificate
    can state its membership claim.
- **H-f · struct TAGS are dropped from the wire** (E-16) though
  spec#Struct_types makes them part of type identity. Preserved through
  substitution, never emitted. **Not probed.** The "same caveat as H-d" the
  first pass attached here no longer means what it did — H-d turned out to be
  observable — so state H-f's own position instead: it is a genuine identity
  collapse in `Ty`, and the plausible witnesses run through either reflection
  (globally refused) or **anonymous** non-empty struct types (refused,
  `wire.go:508`), with named struct types keeping their TypeId. Whether a
  witness exists inside the refusal envelope is **open**, and the honest
  outcome of trying is either a BUG or a recorded argued-unobservable
  narrowing — not a lead left standing.

Two documentation drifts also worth fixing when W7 opens — **both fixed
2026-08-21 (holes arc)**: `docs/2026-08-18_multipackage-identity.md` §6 said
shims are main-package-only, which `load.go:206-218` widened in raft W4.0
(G-35) — the section now records the per-unit injection with the supersession
dated in place; and the `%X` doctrine/code split at `fmtdesugar.go:35` vs
`:516` (G-11) was reconciled by gc probe (doctrine right about gc, code safe
via the parser's `%X` refusal) and the two-site invariant is now named at both
sites — see G-11's residual note.

**One open census question the audit-fix round surfaced and deliberately did
not rule on** (C-42): `emit.go:2413-2416` cites spec#Send_statements for
emitting a send's **channel before its value**, but that section orders both
operands only against the *communication*, and spec#Order_of_evaluation's
left-to-right rule is scoped to "the operands of an expression, assignment, or
return statement" — which does not name the send statement. So channel-vs-value
order in a send may be an E12/E13-class frontend pin rather than a forced
order. The corpus pins one order (`channels/make-edge/ordinary-send-eval-order`,
two calls). **This belongs in `docs/2026-08-11_latitude-inventory.md` as a
census decision, not in a census row** — recorded here so it is not lost, and
flagged so no certificate states C-42's order clause as equality first.

---

## 11. Proposed order for the first translation-validation targets

The criterion is **payoff per unit of proof**, and the highest-payoff targets
are the desugars that have already bitten us: a certificate there retires a bug
*class*, and the regression evidence to test the certificate against already
exists as red-then-green corpus rows.

**Tier 0 — do before proving anything (cheap, shrinks the surface).**
Land H-b and H-c (three small decoder/emitter changes). Each converts an
unchecked emitter obligation into a boundary-discharged free lemma, and H-b is
plausibly a live silent coercion.

Then a key-checking pass over the ~30 wire node shapes — **but not the one this
section originally proposed** (restated 2026-08-21, audit-fix round; the old
text claimed `requireExactKeys` "collapses the whole of §9.2 (rows J-10..J-27)
… in one mechanical pass", and it does not).
- *Why it does not transfer as-is*: `requireExactKeys` (`StrictJson.lean:15`)
  tests **set equality** against a single literal key list. Wire shapes have
  optional keys, and a shape with `k` of them has `2^k` legal key sets — the
  `for` node (`NativeToIR.lean:1163-1205`) has four (`cond`, `post`, `condPre`,
  `init`) beside the required `body`, i.e. **16 legal key sets**, so no single
  expected list exists to pass. Applied with the maximal list it rejects legal
  wires; applied with the minimal one it rejects every optional key.
- *What to build instead*: a **known-keys primitive** — every key present is in
  the shape's declared vocabulary, every required key is present — plus a
  per-shape **key grammar** naming which optional keys the shape admits (and,
  where there are dependencies, which combinations: e.g. `condPre` without
  `cond` is meaningless). The primitive is a dozen lines beside
  `requireExactKeys`; the grammars are ~30 small declarations.
- *What that actually buys, scoped honestly*: it closes the unknown/extra-key
  fail-open (the `"package"` demonstration) and it catches a key **misspelled**
  or emitted under the wrong shape — a real class, and the one that makes the
  decoder's "read key-by-key" style safe. It does **not** collapse §9.2: J-10's
  missing `for.cond` (an infinite loop), J-15's missing `make-chan.cap`
  (unbuffered), J-17's missing `select.default` (blocking) are all *legal key
  sets* by construction, so no key check can see them. Those rows stay emitter
  obligations of the form "key `K` is emitted iff the construct has feature
  `F`", and the honest ways to retire them are per-shape grammars strong enough
  to make absence *illegal* where it should be (e.g. require `cond`, emitting
  `true` explicitly for `for {}`), or a certificate.
- Still worth doing early, and still cheaper than a certificate — just not the
  one-move collapse of §9.2 the first draft advertised.

**1 · C-1, if-init condition-hoist scoping.** *The* place to start. Small, local,
one linear event sequence, one scope; nine dedicated corpus rows plus six
non-affected relatives already pinned green; BUG-058 gave three observable modes,
two of them silent wrong answers, on `if v, ok := m[k]; ok && f(v)` — one of the
most common shapes in real Go including `deps/raft`. If a certificate cannot be
made to work here, the route is in trouble, and finding that out costs a week
rather than a quarter.

**2 · B-42/B-44/D-1, the comma-ok family.** BUG-034, BUG-057 and the
**arity-gated** map-get seam (B-44 — the `map-get` tag is explicit; what is
implicit is that `lhs.size == 2 && rhs.size == 1` means "comma-ok map read"
and can mean nothing else) all live here. Two extra payoffs beyond the bug
class: it forces the certificate to span **stage 1 and stage 2** (the shape
recognition is the decoder's), and it forces the wire's implicit contracts to
be written down.

**3 · A-9 + J-38, shadow-capture pre-binding.** The only obligation in the census
that is both genuinely non-local and a demonstrated near-miss, with one arm still
fail-closed rather than solved. It is also the cleanest demonstration of what
translation validation buys that a gate cannot: the decoder's declaration-before-
RHS ordering and the emitter's compensating pass are in two languages and nothing
relates them.

**4 · F-8 + J-28, the gid ↔ globals correspondence.** The cleanest *statable*
lemma in the census: one emitter source (`collectGlobals`), half the property
already checked at the boundary, and a recorded audit (C1) proving the failure
mode is a silent wrong answer rather than a stuck.

**5 · D-7, the key-grammar injectivity lemma.** A self-contained string-grammar
theorem that a dozen rows cite (D-4, D-6, E-26, E-28, J-43, and every synthetic
FuncId constructor). Prove once, reuse everywhere. Good second-week work for
whoever is building certificate infrastructure rather than semantics.

**6 · B-1, short-circuit `&&`/`||`.** The first genuinely hard one — conditional
execution of an arbitrary effect prefix — but its fidelity argument was written
*before* the implementation (g2.md's "E3 — THE FIDELITY ARGUMENT"), so the
informal proof already exists and the certificate is a mechanization of a written
argument rather than a fresh one.

**7 · C-11/C-12, the switch selection-index machine.** The first row where the
certificate needs a real invariant (relating `$swi`/`$swf` valuations to "which
clause Go selected / whether fallthrough is armed") rather than a trace
alignment. Well-pinned (14 corpus rows) and self-contained.

**Deliberately NOT first**, despite being the most valuable eventually:
**A-1** (the ANF pass). It is the crux and everything depends on it, but its
statement is a *membership* claim over the AST semantics' permitted set (§0.2
K2), and getting that statement right needs the spectec side to have a
nondeterministic evaluation-order relation — which is a W7 design question
(§12), not a proof task. Attempting A-1 before §12.2 is settled will produce a
certificate that proves equality with a gc-pin, i.e. exactly the doctrine
violation the whole project is organized against.

Also deliberately not first: **C-20/C-21/C-22** (goto restructuring). Hardest
control-flow transformation in the frontend, and its real obligation is the
*sufficiency of the four-check envelope* rather than the transform itself — a
non-interference argument about programs the transform refuses.

---

## 12. Open design questions for W7

**12.1 · Wire-level or AST-level simulation — and what to do about the third
stage?** The plan of record says "spectec-AST semantics ≃ GoCore semantics of the
emitted wire". §0.3 shows the lowering is three stages, and stage 2
(`NativeToIR.lean`) owns real semantic content — the range desugars (C-7), the
comma-ok shape recognition (B-44), the declaration-before-RHS ordering (J-38),
the `for`-post placement (C-3). Three shapes are available:
(a) **end-to-end** — relate the source AST directly to the GoCore program, so
the wire is an implementation detail and stage 2 is inside the certificate;
(b) **two-stage** — a wire-level intermediate semantics, with AST≃wire and
wire≃GoCore proved separately, which needs a *third* semantics nobody has
written; (c) **stage-2-trusted** — certify AST≃wire only, leaving the decoder in
the TCB, which is cheap and wrong (four of the six §10 holes are stage-2 or
stage-1/2-joint). Recommendation, for the record: (a), with §9's rows as
*side conditions on the wire* — discharged by the boundary checks Tier 0 adds
**where a key check can reach them**, and carried as explicit side conditions
where it cannot (§11's restated Tier 0: §9.2's optional-key rows are legal key
sets by construction and survive any key check).
Stage 3 (the shim/shadow-model re-entry, G-28/G-35) is not covered by any of the
three and needs its own answer — the certificate's subject program is not the one
the user wrote.

**12.2 · How does the spectec side represent evaluation-order latitude?**
This gates target A-1 and is the single most consequential question here. Our
adopted reading is **UNSEQ** (I-2, ledger L-013): spec silence admits
interleavings of the unordered events' observable sub-events, not merely a
per-expression choice between total orders. If the spectec-derived semantics is
a deterministic interpreter — SpecTec's own backend runs latitude points as
`EitherI` with backtracking, i.e. **a deterministic pin**
(`docs/2026-08-17_prior-art-spectec.md` §1, caveat 3) — then the simulation can
only be equality with one member, and every K2 row in this census — the
corrected set of **13**: A-1, B-6, B-19, B-27, C-34, C-36, C-38, C-40, D-11,
F-2, F-3, F-6, F-7 (§0.2) — becomes a certificate that freezes a gc-pin as a
fidelity claim. The doctrine forbids exactly that. The two **K2m** rows (C-7,
J-39) are not exposed the same way: their envelope lives in GoCore, so what
they need from the spectec side is only that the frontend obligation
("preserve the choice structure, narrow nothing") is statable. So: **the spec
document needs a nondeterministic reduction relation at the E-series points,
and the certificates need to be membership statements.** If that is too
expensive for the prototype, the honest interim is to certify the *forced*
rows (K1) and mark the K2 rows explicitly out of certificate scope — never to
certify them against the pin. C-38 is the worked example of doing this at the
level of a single row rather than a whole row-set: three conjuncts certified as
forced, the fourth either stated as membership or declared out of scope, with
E13's "NO PIN MAY BE TAKEN HERE" quoted in place so the split cannot quietly
close.

**12.3 · How are the shims specified?** §7's 35 rows are `REFINE(pkg.Fn, D)`
obligations against **documented library behavior**, not against the language
spec — there is no Go AST to simulate and the differential is a lower bound only
(G-16 is a *recorded silent divergence* with, by construction, no corpus row).
Three options: (a) leave them outside the spec entirely, so a certificate's
domain excludes any program calling a shimmed function — clean, and immediately
excludes raft; (b) write spectec-side **axiomatic specifications** for the
modeled domain, making the shim's Go source a *proof obligation against the axiom*
and the domain boundary a first-class object; (c) treat the injected Go source as
ordinary source, certify it like any other program, and accept that the
certificate then says nothing about whether the shim matches the stdlib.
Note (c) is what the current architecture does implicitly, and it is the option
that leaves G-16, G-18 and G-23 unaddressed. Recommendation: (b) for the four E5
shims and the Builder model, (a) for fmt (whose modeled domain is already carved
out by a constant-format refusal, G-2 — the one place where the coverage bound is
genuinely clean).

**12.4 · Where do quarantine stubs sit in the spec's semantics?** §8's contract
(K4) is not a simulation: the stub says "any call here refuses visibly and
nothing else changes". A spectec-derived semantics of *Go* has no such
construct. Options: (a) the certificate's **domain** excludes any program
containing a quarantined declaration — clean, but note that a stub also carries
an exact method-table entry that *does* affect satisfaction answers reachable
from non-quarantined code (H-1), so "excluded" is not the same as "absent";
(b) the spec grows an explicit `stuck`/`unsupported` outcome and the simulation
is stated up-to-`stuck` (the certificate proves "either both terminate with the
same observation, or ours refuses"), which is a *weaker but honest* theorem and
composes with the fail-closed doctrine; (c) prove the stronger property that a
program whose reachable call graph avoids all stubs behaves as if they were
absent — provable, but it needs the reachability analysis F-11 already
implements, conservatively. Recommendation: (b) as the default statement shape,
with (c) available for programs that clear F-11's closure.

**12.5 · Which side models memory layout?** E-13: the frontend has no size,
alignment or offset model at all and GoCore's heap is `Loc`-keyed, never
byte-addressed. If the spectec Go document models layout, every certificate is
stated modulo a quotient; if it is abstract too, the row is free. Cheap to decide
now, expensive to retrofit.

**12.6 · Does the certificate re-derive go/types, or inherit it?** E-24 records
that instantiation resolution, `InitOrder` (F-1), constant folding (B-13) and
every type annotation (E-15) are delegated to go/types — and that the
differential **cannot see a go/types inference bug** because gc uses the mirrored
types2 (**shared fate**, recorded honestly in the generics note §2d). A
spectec-derived typing judgement would be the first independent check of that
surface. Whether W7 wants that is a scope decision, not a technical one, but it
should be made deliberately rather than by default.

---

## 13. Counts

| chapter | rows |
|---|---|
| A · normalization core | 10 |
| B · expressions | 45 |
| C · statements and control flow | 44 |
| D · declarations, scoping, identity | 13 |
| E · types, method sets, generics | 36 |
| F · packages, initialization, globals | 15 |
| G · library models | 35 |
| H · quarantine and fail-closed contracts | 6 |
| J · decode-half wire invariants | 45 |
| **total** | **249** |

Chapter C moved 41 → 44 (and the total 246 → 249) in the 2026-08-21 audit-fix
round: C-42 (send statement), C-43 (statement-position sync ops), C-44
(`once.Do`) — three lowerings the first pass missed entirely, §3.9.

By obligation kind, **K2 is the one that is counted exactly** because it is the
one the doctrine cares about: **13 rows** — A-1, B-6, B-19, B-27, C-34, C-36,
C-38, C-40, D-11, F-2, F-3, F-6, F-7 — plus **2 K2m rows** (C-7, J-39) where
the latitude is the machine's and the frontend's duty is not to narrow it.
*This register was wrong in the first pass and is the audit-fix round's largest
correction*: it listed 9, of which C-7 and J-39 do not meet §0.2's own
definition (the frontend is not the choice site) and F-2 was missing despite
being tagged K2 in its own row header, while five further rows (B-6, B-19,
B-27, C-36, C-40) were tagged plain K1 although their order clauses are
frontend realizations of E3/E4/E12/E13 — the misclassification in the **worse**
direction, since a K1 tag invites a certificate to state equality with a
gc-pin. The other kinds stay approximate: K1 (forced-order simulation) ~150,
K3 (library refinement) 35, K4 (partiality/fail-closed) ~25, K5 (wire
invariants) 45; several rows carry two kinds.

The **L set is enumerated** (33 rows) rather than tallied, since it is the
planning-relevant one — every row here has a correctness statement that is not
a value equality:

> A-1 (ANF membership) · A-8 (closure conversion) · B-1 (short-circuit) ·
> B-8 (generic call) · B-11 (interface boxing, 37 sites) · B-35 (promoted
> receiver path algebra) · C-4 (loop-var trigger completeness) · C-5
> (per-iteration cell identity) · C-11 (switch index machine) · C-18 (select
> delivery) · C-20 (goto restructuring) · C-21 (the goto envelope's
> sufficiency) · **C-34 (call-RHS arity/order routing)** · C-38 (chan-recv
> phases) · **C-44 (`once.Do`'s two-frame desugar)** · D-8 (display vs
> identity, not frontend-fixable) · E-13 (layout, conditional on §12.5) ·
> E-17 (satisfaction completeness) · E-18 (promotion flattening +
> method-table completeness) · E-23 (monomorphization) · F-2 (hidden init
> dependencies) · F-3 (the pruned schedule) · F-7 (init order is latitude) ·
> F-12 (H-11 skip soundness) · G-5 (fmt effect-trace order) · G-11 (gc
> dispatch precedence) · G-16 (typed-nil error, to close) · G-18 (the
> recover-frame split) · G-23 (byte-scan ≡ rune-scan) · G-28 (shadow-model
> merge) · H-4 · J-29 (call typing) · J-38 (shadow capture).

C-34 was tagged L in its own row header but omitted from this enumeration
(31 → 33 with C-44, corrected 2026-08-21). S/M are not counted; the per-row
tags carry them.

Holes: 6 (§10) — **2 confirmed live silent wrong answers** (H-a, H-d, both
predating this branch and both owing a BUG id), 1 refuted-as-divergence (H-e,
now a latitude-census gap), 1 unwitnessed (H-b), 1 restated as a proposal
rather than a defect (H-c), 1 unprobed with observability open (H-f).
Documentation drifts: 2 (§10). Open census questions handed to the latitude
inventory rather than ruled on here: 1 (C-42's channel-vs-value order, §10).
Cross-file invariants nothing checks: 3 (`%X` parser↔dispatch,
`%T`-refusal↔`errors.New` identity, emitter↔decoder `$`-prefix disjointness).

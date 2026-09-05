# The method-set record contract (class closure of BUG-053)

Date: 2026-08-10. Branch `spec-parity`, arc-end class-closure round
(user direction of the same date: the BUG-053 fix closed the INSTANCE —
sync stubs — not the CLASS; "it shouldn't be possible to fail that
way"). This is a wire-format + boundary change; recorded here per the
capture-decisions rule. Companion records: BUGS.md BUG-053 addendum,
`docs/2026-08-09_sync-package-design.md` §7/§11.

## 1. The class

The machine read an absent/empty method table as a CORRECT empty method
set. `dynamicMethodSetRecorded` (Ops.lean) keyed on the TYPE-KIND
TAXONOMY: `.defined` names consulted TypeDef presence (BUG-008/BUG-009's
guard), and every OTHER kind fell to a blanket `true` justified as
"types that are not `.defined` can carry no methods in Go at all". That
justification was true of the kinds the author had in mind (slices,
maps, basics, `**T`) and FALSE of the taxonomy as a guard: any kind
added later that models a method-carrying Go type inherits the blanket
`true` and silently answers definite wrong "no"s on
type-assert/type-switch/satisfaction — the worst class, status ok,
invisible to every green gate. `Ty.sync` was the first instance (the
four sync primitives model gc DEFINED types with real method sets); a
future imported family, a new frontend path, or tomorrow's
re-introduction of today's bug are the next ones. Absence of knowledge
must never be an answer.

## 2. Which type kinds can carry method sets (gc-probed)

Go spec (Method declarations): a receiver's base type must be a DEFINED
type declared in the same package, and not a pointer or interface type.
Probed 2026-08-10 (`.tmp/probes/carriers`, go1.26.5):

- defined types over int / slice / map / func / chan / array / struct
  underlyings all carry methods and satisfy interfaces through them
  (`kinds.go`: all seven `true`);
- a defined POINTER type cannot (`ptrbase.go`:
  `invalid receiver type P (pointer or interface type)` — the same
  refusal covers interface base types);
- unnamed type literals carry no methods (`literal-slice: false`);
- `*T` inherits `T`'s value-receiver methods (one pointer level; `**T`
  carries nothing — probed 2026-07-30, design note Q3 / audit finding 4).

Mapped onto GoCore's `Ty` (after ONE pointer deref, mirroring the
method-set base the lookups use; `resolveDefinedAliases` was deleted by
C2, 2026-09-05 — every `Ty` on the machine is alias-free since the
frontend inlines aliases, and `.defined` is a table INDEX, `Ty.defined
(idx : TypeIdx)`, whose key is read back from the entry):

- **carriers** — `.defined idx` (every user/imported/mono-stenciled
  named type; key = the `TypeId` beside table entry `idx`, and an index
  the table lacks maps to an UNRECORDABLE marker key so its queries
  refuse — audit fix R1, 2026-09-05) and `.sync kind` (models the gc defined types
  `sync.Mutex`/`RWMutex`/`WaitGroup`/`Once`; key `sync.<Kind>`);
- **non-carriers, correct by the LANGUAGE (not by registration)** —
  `.bool`/`.int`/`.float`/`.string` (the unnamed predeclared types;
  named basics are `.defined`), `.slice`, `.map`, `.array`, `.chan`,
  `.funcType`, `.pointer (.pointer _)`, `.pointer (.interface _)`,
  `.unsupported` (never a dynamic type; boxes refuse upstream);
- `.interface` — not a method CARRIER in this sense: an interface's
  declared requirement set lives in its `interfaceDef`, and a box's
  dynamic type is always concrete, so interface Tys never reach the
  carrier lookup as `dynTy`.

Any FUTURE `Ty` kind that models a defined Go type must join the
carrier arm — and the fail-closed default means forgetting to emit its
records yields visible refusals, never wrong answers (the exact
inversion of the old blanket `true`).

## 3. The contract

1. **The frontend emits an explicit method-set record for EVERY type
   that can carry methods** whose identity reaches the wire: a new
   REQUIRED top-level wire field
   `"methodSets": [{"type": <key>, "coverage": "full"|"exported"}]`.
   Empty-but-present means genuinely empty. Emission completeness per
   carrier kind, argued:
   - locally declared named types (mono-stenciled included): one record
     per non-interface TypeDef, `coverage: full` — the wire contract
     already requires the FULL method table for every declared named
     type, promoted methods included (D2, 2026-08-05); a method whose
     body cannot lower still lands as a signature-carrying quarantined
     stub, so the SET is complete even when calls refuse;
   - D5 imported marker types: `coverage: exported` per marker TypeDef
     (the wire cannot express cross-package unexported method identity);
   - sync primitives: `coverage: exported` per type reaching the wire
     (`syncMethodStubs`' sets are the exported pointer method sets);
   - where the frontend cannot emit a type's true method set (D5's
     skip-whole), NO record is emitted and every query on that type
     REFUSES at the machine (below) — the refusal moves to the first
     program point that could OBSERVE the missing set, since
     observability (a box being queried) is dynamic and undecidable at
     export time. Carriers with no skip lane at all (sync) keep the
     BUG-053 fail-the-export posture as belt and suspenders.
2. **The machine answers satisfaction/dispatch ONLY from a record.**
   `methodSetCoverage?` consults `ExecState.methodSets` exclusively;
   for a queried carrier with NO record, `firstUnsatisfiedMethod?` and
   `dynamicDispatch?`'s no-method arm refuse `.unsupported` (a visible
   frontend-blocked classification — never a definite yes/no, never
   stuck, never a panic). The positive direction stays sound as before
   (a recorded matching method really is in the set); `coverage:
   exported` refuses definite-"no" answers that hinge on an unexported
   requirement (D5 semantics, now record-keyed). The non-carrier arm's
   empty-set answer is justified by §2's language argument, which no
   registration can invalidate. Interpreter and relation share the
   lookup helpers (satisfaction runs inside the shared `Except` ops
   layer), so lockstep is by construction.
3. **The wire boundary pins the class forever**: hand-crafted-wire
   fixtures (Tests/GoCoreEval) — a method-carrying `.defined` type with
   a TypeDef but NO methodSets record refuses satisfaction (proving the
   guard keys on the RECORD, not TypeDef presence); a `.sync` box with
   no record refuses (the re-introduction pin); the same wire WITH the
   record answers (mutation sensitivity — the refusal is the record's
   absence, nothing else). Plus: the BUG-053 red-first corpus pins stay
   green, and NO current corpus id changes classification (the contract
   is vacuously satisfied by today's frontend, which emits records for
   every carrier it can emit).

## 4. Decisions and consequences

- **`Program.methodSets` + `ExecState.methodSets`** (defaults `#[]`):
  a state built without records FAILS CLOSED on every carrier query —
  the safe default for hand-built states (eval tests query satisfaction
  only through the always-true empty interface today; a future
  eval program that boxes and asserts must populate records
  explicitly).
- **The decoder synthesizes `("struct{}", full)`** alongside the
  canonical empty-struct TypeDef it already injects (the set idiom's
  `struct{}` is a carrier by kind and genuinely method-free).
- **`methodSets` is REQUIRED and strictly decoded** (entry shape,
  coverage enum, duplicate keys refused): an old wire — or a new
  emitter that forgets the field — refuses at decode, not at query.
- **Renderer joins the closure**: `renderPanicPayload`'s defined-type
  `main.T(v)` arm requires a record before trusting
  `panicPayloadIsRewritten`'s "no Error()/String()" answer — the same
  absence-as-answer class, one consumer over (fail closed to `none`,
  an unrenderable abort, never a fabricated message; `Error`/`String`
  are exported names, so `exported` coverage suffices to decide).
- **Pinned lowering terms regenerate** (9 imported-goose R2 pins, 3
  golden pins + repr baselines): `Program` gained a field, so every
  pinned `repr` moves — regenerated in the same change with this note
  as the reason, per the pin scripts' own discipline.
- **Retirements**: `dynamicIsImportedMarker` (TypeDef-kind sniffing) is
  replaced by record coverage; `dynamicMethodSetRecorded`'s taxonomy
  arm survives ONLY as the carrier/non-carrier split of §2, whose
  non-carrier half is a language fact, not a registration default.
- **Designated statements: source byte-identical, meaning refined
  fail-closed.** The 44 designated statements' SOURCE is untouched.
  `ExecState` gained the defaulted `methodSets := #[]` field, so the
  surface judgments (`GoSpec`/`GoSpecT`/…, which build their states
  with structure-literal defaults) now quantify runs with EMPTY
  records — a conservative refinement: a verified program that queried
  satisfaction on a carrier would refuse under `#[]` (failing the
  proof, never satisfying it vacuously — Progress/Terminates would not
  discharge), and no current designated subject queries satisfaction
  (all 256 proof jobs, including the kernel-evaluated `Terminates`
  discharges, re-verify unchanged). The two adequacy-internal
  `ExecState.mk` sites were updated to spell the same `#[]`
  explicitly. When a surface subject someday needs satisfaction, the
  judgments should grow an explicit records parameter — a deliberate
  statement change with its own review, not a default.

## 5. Known limitations (recorded at the S6 audit fix round, 2026-08-10)

- **Proof-side seeds diverge from the driver-built states — recorded,
  with the divergence's live half fixed forward.** §4's "meaning
  refined fail-closed" bullet states the general case; the sharper
  fact it left implicit: the pinned `Program`s' record arrays are
  NON-EMPTY (every decoded wire carries at least the synthesized
  `("struct{}", full)`, and e.g. `quorumLowered` carries 4 records,
  `muxerLowered` 3), so every proof-side structure-literal seed
  (`importedSeed`, `chanSeed`, the TotalPins literals, the surface
  judgments' states) ACTIVELY drops records the executable drivers
  (`runProgramSetupM`/`CLI.enumSetup`) thread through — not merely
  defaults an absent thing. The direction is strictly-more-refusing
  (all three record consumers refuse under `#[]`; the audit's A/B runs
  reproduced identical results with and without records on every
  shipped subject), so no shipped claim is wrong; the transfer
  argument ("a run that completes under `#[]` made no carrier query,
  hence exists identically under the real records") is PROSE — the
  `empty-records-refuse-strictly-more` lemma is owed WITH its first
  consumer, the first R3 walk over a record-carrying seed.
  Fixed forward: `scripts/gen-imported-pin` now emits
  `methodSets := <term>Lowered.methodSets` in every generated seed
  (S6 audit fix), so future pins match the drivers; the two pre-S6
  pin modules (`ImportedGooseNew`/`Vars`) deliberately keep the
  empty-record seed their R3 kit compositions bind to (the generator
  header records the regeneration consequence).
- **Promoted unexported methods from imported embedded types are
  re-keyed to the local type under `full` coverage** (audit note,
  latent): `synthesizePromotionWrappers` emits promotion wrappers for
  UNEXPORTED methods inherited from an imported embedded type keyed on
  the LOCAL type, while the stub passes deliberately skip unexported
  imported methods (cross-package unexported identity is inexpressible
  on the name-keyed wire) — and the local type's `full` record then
  licenses definite answers over a method set that includes the
  re-keyed name. gc scopes unexported interface requirements to the
  declaring package (probe: a main-package interface requiring
  `copyCheck()` is NOT satisfied by `struct{ strings.Builder }` —
  gc says false; a name+signature match would say true). CURRENTLY
  UNREACHABLE end-to-end: every probed shape refuses earlier
  (`default value for imported named type ...`), and the sync
  carriers emit exported-only sets, so no wrong answer exists today.
  The honest fix when a case reaches it: package-scoped method
  identity on the wire, or refusing promotion of unexported imported
  methods — a frontend capability decision, not a record-contract
  change.

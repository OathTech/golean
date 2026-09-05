package main

// wire.go emits the native wire schema: a typed Go AST (Go's grammar with
// go/types types attached and names resolved). The Lean side
// (GoLean/NativeJson.lean + NativeToIR.lean) decodes it strictly and lowers it
// to GoCore. Keeping the wire a faithful typed Go AST — rather than
// pre-desugared GoCore — keeps this emitter a mechanical serializer and
// concentrates the semantic GoCore mapping in Lean, which stays authoritative
// and extends one construct at a time.

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strings"
)

// emitter walks a type-checked package and produces wire nodes (Go values
// ready for JSON encoding: map[string]any / []any / scalars).
type emitter struct {
	fset *token.FileSet
	info *types.Info
	pkg  *types.Package

	// A-normal form: calls and allocations in expression position are hoisted
	// into let-bound temp statements accumulated here for the statement being
	// emitted, so GoCore expressions stay pure (calls are statements).
	hoisted []any
	tmpSeq  int

	// localRenames: function-local variables renamed because their name
	// collides with a NAMED RESULT of the enclosing function (the wire's
	// name channel would alias them at the return/frame-exit seam —
	// resultshadow.go). Object-keyed; rebuilt per function/lit body.
	localRenames map[types.Object]string
	// hoistForbidden is non-empty exactly where hoisting a call or an
	// allocation OUT of the expression would change evaluation order.
	// TODAY THE ONLY SETTER IS THE SHORT-CIRCUIT RHS (emitBinary; the
	// same statement of fact is at that site) — the old "short-circuit
	// RHS, loop cond" here named a loop-condition setter that does not
	// exist, corrected 2026-08-16 by the post-autonomy audit. The
	// checks that read it are written to keep any FUTURE
	// hoist-forbidden position fail-closed rather than silently
	// normalized. It is a property of the enclosing STATEMENT CONTEXT
	// and does not cross into a lifted function body: emitFuncLit
	// clears and restores it (audit R2A-F2, guardrails in
	// Corpus/coverage/exec/bools/short-circuit-funclit).
	hoistForbidden string
	// scHoistOK admits the single hoist() temp-binding path (plain call
	// temps and kin) while hoistForbidden is set for a SHORT-CIRCUIT RHS:
	// emitBinary captures those hoists into its own accumulator and wraps
	// them in the conditional that realizes the spec's "the right operand
	// is evaluated conditionally" (E3, docs/gallery-campaign-log/g2.md,
	// "E3 — THE FIDELITY ARGUMENT"). Every OTHER quarantined effect site
	// (channel receives, make/new/append/copy, slice/map literals,
	// &composite, interface method values, multi-value splats) checks
	// hoistForbidden directly and keeps its standing fail-closed refusal.
	scHoistOK bool

	// Lambda lifting (W5, docs/2026-07-24_sequential-coverage-scoping.md §8):
	// func literals are hoisted to synthetic top-level functions taking their
	// captured variables as POINTER parameters, so Go's capture-by-reference
	// is explicit in the lowering. `lifted` accumulates them; `captureParam`
	// maps a captured variable to its pointer-parameter name while emitting a
	// lifted body, so references to it become derefs.
	lifted       []any
	liftSeq      int
	curFuncName  string
	captureParam map[types.Object]string
	// The enclosing function's result tuple, for the return-site
	// interface-conversion wrap.
	curResults *types.Tuple

	// Whether the `defer recover()` no-op function has been registered.
	deferNoopEmitted bool

	// nodeStarts (latitude E13 option (b), lane e13-b 2026-09-05 — design
	// docs/2026-09-05_e13-b-design.md §4): the hoist-accumulator length at
	// entry of every emitExpr node still being emitted, innermost last.
	// `pushHoist` (the ONE way an event's statement joins the accumulator)
	// first drops the trailing `unseq-probe` entries appended since the
	// current node's start — those are probes of the node's OWN operands,
	// which the event's statement evaluates itself (the FORCED "arguments
	// before the call" position never gets a probe). Swapped with the
	// accumulator wherever the accumulator is swapped inside an expression
	// (the short-circuit RHS; a lifted func-literal body).
	nodeStarts []int
	// probeSuppress > 0 while an assignment TARGET (E2/E3/E4's axes, not
	// E13's) is being emitted: no unseq-probe is appended for its operands.
	probeSuppress int
	// probedNodes records every AST node for which emitExpr APPENDED an
	// unseq-probe (whether or not a later pushHoist/prune dropped it — a
	// dropped probe means the operand sits in a FORCED position, which is
	// covered by the event that evaluates it). The narrowed A6 guard
	// (`unprobedPanickyBefore`, e13-b audit fix round R1) walks a sweep
	// for panicky non-call material that is NOT in this set: material in
	// an assignment/IncDec/compound target, an address-of or receiver
	// operand (probeSuppress), or an operand containing recover() / an
	// allocating conversion — the positions the E13 (b) envelope does not
	// probe, where a len/cap/make hoist would still realize only the
	// events-first order. Keyed by node identity; never reset (nodes are
	// unique; stencils re-emit the same nodes with the same structural
	// answer).
	probedNodes map[ast.Expr]bool

	// sweepStmt is the AST node whose emission owns the CURRENT hoist
	// accumulator (the "sweep"): the statement in emitStmtList, or the
	// sub-node at every site that opens a fresh accumulator (if/for
	// conditions and init/post, switch tags and case values, range
	// operands, short-circuit RHS, per-spec var initializers,
	// assignment-target probes). It is the SCAN SCOPE for the A6
	// ordered-event predicate (emitBuiltin, sweepOrderedEventAfter):
	// spec#Order_of_evaluation orders "all function calls, method
	// calls, receive operations" lexically left-to-right, and
	// spec#Built-in_functions says built-ins "are called like any
	// other function" — so a len/cap/min/max must hoist exactly when
	// an ordered event (receive or call) lexically FOLLOWS it in the
	// same sweep: those events hoist, and an inline builtin would
	// otherwise evaluate after them, reading state the later event
	// already changed (BUG-062: a spec-FORCED silent wrong value/
	// panic order). Events in a DIFFERENT sweep (a loop body vs its
	// condition) cannot reorder against this one, which is why the
	// scope is the sweep — not the function (the retired fnHasRecv
	// era, whose function-wide receive flag both missed calls
	// entirely, BUG-062, and over-refused panicky len operands in
	// statements with no event at all, BUG-032/F23).
	sweepStmt ast.Node

	// Label usage of the CURRENT function body (control-flow slice,
	// docs/2026-08-04_control-flow-design.md), computed by scanLabelUses
	// before the body is emitted and saved/restored around nested func
	// literals (a label's scope never crosses a function boundary):
	// labels referenced by labeled break/continue, and by goto.
	branchLabels map[string]bool
	gotoLabels   map[string]bool

	// Goto dispatch context (stage 3, emitGotoBody): segment index per
	// top-level goto-target label, the program-counter variable, and the
	// dispatch loop's machine label. A `goto` lowers to
	// `$pc = seg(L); continue-to $gotoN`. Nil outside a restructured
	// body, so a goto with no context fails closed.
	gotoSeg  map[string]int
	gotoPC   string
	gotoLoop string

	// Function-LOCAL type declarations (`type T ...` in a body): they
	// register in the global type table (type declarations have no
	// runtime effect — legal for goto to jump over), with a program-wide
	// duplicate-TypeId refusal in emitProgram.
	localTypeDefs     []any
	localIfaceMethods []any

	// Identity vs display (docs/2026-09-05_fr19-bug097-design.md §0):
	// the display record of every minted TypeId key (identity.go
	// noteTypeDisplay) — attached to every TypeDef by emitProgram; a
	// key registered with two displays refuses (displayConflicts).
	typeDisplays     map[string]typeDisplay
	displayConflicts []string
	// Scope ordinals of FUNCTION-LOCAL type declarations (design note
	// §2.2), built once per program by localTypeOrdinal; a local type
	// outside the table is recorded for the fail-closed refusal.
	localOrdinals map[*types.TypeName]int
	badLocalTypes map[string]bool
	// BUG-098 guard input: unexported requirement name -> declaring
	// package paths (identity.go noteUnexportedRequirements).
	unexportedReqs map[string]map[string]bool

	// Interface-receiver methods CALLED somewhere in the package, keyed
	// "<IfaceName>.<Method>" (the exact func id the call emits). Interfaces
	// declared in the package anchor their methods via emitGenDeclTypes;
	// predeclared ones (error) and, later, imported ones have no decl here,
	// so emitProgram synthesizes their table entries from this record.
	calledIfaceMethods map[string]calledIfaceMethod

	// EVERY interface type that reaches the wire, keyed by its wire name.
	// Recorded at the single type choke point (emitType) plus the
	// declaration loop, so an interface referenced only as an assert TARGET
	// is captured too. emitProgram turns each into an `interface` TypeDef
	// carrying the FULL method set — the machine's interface-satisfaction
	// requirements. Before this, requirements were derived from the DISPATCH
	// table, which holds only methods actually CALLED, so an interface with
	// no call site had an EMPTY requirement list and every dynamic type
	// vacuously satisfied it (pre-merge audit 2026-07-31, finding 0).
	seenInterfaces map[string]*types.Interface
	// Wire names registered with NON-IDENTICAL interfaces (noteInterface);
	// non-empty refuses the export in emitProgram's declaration pass.
	ifaceConflicts []string

	// Every NAMED STRUCT type declared in the package (package-level and
	// function-local), collected by emitGenDeclTypes for the promotion
	// wrapper pass (design note 2026-08-05 D1.3): emitProgram synthesizes
	// forwarding wrappers for each promoted entry of the type's method
	// set, so the machine's flat method table is COMPLETE and a missing
	// method is real information (D2).
	namedStructTypes []*types.Named

	// Every IMPORTED named non-interface type whose identity reached the
	// wire (design note 2026-08-05 D5): emitProgram emits, per type whose
	// EXPORTED method set is fully emittable, an `unsupported`-marker
	// TypeDef (existence only — structural use keeps failing closed) plus
	// signature-carrying method STUBS, so interface satisfaction can
	// answer instead of refusing (BUG-009's polarity).
	importedNamed map[string]*types.Named
	// The importedNamed entries importedTypeDecls has already emitted
	// (audit fix round M1): the pass runs before AND after the interface
	// fixpoint, emitting each type once.
	importedDeclsDone map[string]bool

	// SIGNATURE-OPAQUE mode (FR-23, 2026-09-04): while set, an
	// instantiation of an IMPORTED generic type (`iter.Seq[int]`,
	// `iter.Seq2[K,V]`, any stdlib `pkg.G[...]`) emits as an opaque
	// `named` reference under its mangled TypeId instead of refusing,
	// and the key is recorded in opaqueInsts for an existence-only
	// `unsupported` marker TypeDef (the D5 shape). Set ONLY around
	// signature emission for declarations whose bodies never lower —
	// quarantined method stubs, interface requirement lists, promoted-
	// method stubs — so a VALUE of such a type never exists in the
	// machine: satisfaction answers (identical keys ⇔ identical Go
	// types, the mangler's injectivity), a CALL refuses by name, and a
	// body that would construct or consume the value refuses at its
	// own emitType (this flag is off) and quarantines per declaration.
	sigOpaque   bool
	opaqueInsts map[string]*types.Named
	// FR-25 (2026-09-04, lane fr24; [USER]-approved rider, relayed): in
	// the same SIGNATURE-OPAQUE mode an unlowerable BASIC type
	// (complex64/complex128 — FR-15's kinds; unsafe.Pointer — out of
	// language) emits as an opaque `named <basic>` marker under the
	// basic type's own spelling and is recorded here for an existence-
	// only `unsupported` TypeDef (opaqueMarkerTypeDefs). A basic type has
	// NO methods, so the marker is honest by construction (the fr22-fr23
	// audit's item-7 rule): satisfaction over a requirement list or a
	// stub that mentions it answers exactly, a VALUE of the type never
	// exists in the machine (emitBasic refuses with the flag off), and a
	// CALL of the declaration refuses by name (the stub's reason).
	opaqueBasics map[string]*types.Basic
	// The markers the CURRENT withOpaqueSigs window touched (minted OR
	// re-used — a key first minted by an interface requirement list is
	// still the reason a later method stub fails closed), so every stub's
	// reason names its own markers. Reset per window.
	opaqueTouchedInsts, opaqueTouchedBasics map[string]bool

	// The modeled sync primitive types whose identity reached the wire
	// (arc-end fix round 2026-08-10): emitProgram emits, per type, its
	// FULL exported (pointer) method set as declaration-only stubs —
	// satisfaction answers what gc answers; a CALL through a stub
	// refuses per-stub. Unlike importedNamed this pass FAILS THE EXPORT
	// on an un-emittable signature: `Ty.sync` is not a `.defined`
	// marker, so the machine has no not-recorded refusal lane for it —
	// a silently skipped sync method set would answer a false "no"
	// (the arc-end CRITICAL's exact mechanism).
	syncUsed map[string]*types.Named

	// "Prim.Method" pairs emitSelector value-lowered against the bodied
	// stub promise (audit fix round 2026-09-01, F2): recorded at each
	// method-value lowering (value = first-seen source position),
	// cross-checked in syncMethodStubs against the ACTUALLY-BODIED set
	// — a demanded pair whose stub got no body (a stdlib signature
	// drift under a future pin) FAILS THE EXPORT there, instead of
	// landing as a runtime refusal on a bodiless stub.
	syncValueLowered map[string]string

	// Mangled instantiation key → the types.Type it names (mono.go, the
	// generics slice): the belt-and-suspenders collision registry behind
	// the mangling injectivity argument, capped at monoRegistryCap. Every
	// mangled key passes through registerMangledKey exactly once per
	// spelling.
	mangledKeys map[string]types.Type

	// Monomorphization state (mono.go, generics design note 2026-08-05).
	// curSubst is the ACTIVE stencil substitution (declaration type
	// parameter → concrete argument), nil outside stenciling; substErr
	// records the first substitution failure surfaced as an Invalid type
	// (emitType refuses on it — fail closed). genericFuncDecls maps each
	// generic function object to its declaration for the worklist;
	// funcInsts/funcInstQueue are the dedup map and pending queue of
	// stencils; monoCtxt is the shared types.Instantiate context.
	curSubst         map[*types.TypeParam]types.Type
	// curTargs mirrors curSubst as the ORDERED argument list of the
	// active instantiation (nil outside stenciling) — consumed by
	// qualifiedTypeName to parameterize TypeIds of function-local type
	// declarations (arc-final audit F3).
	curTargs []types.Type
	// curInstDecl is the generic declaration whose stencil is being
	// emitted (nil outside stenciling): qualifiedTypeName parameterizes
	// ONLY the local types declared INSIDE it (BUG-018), not every
	// function-local type the stencil body mentions — a local type
	// passed AS a type argument (`cmp.Compare[main.score·1]`, FR-19) is
	// declared outside and keeps its own key (lane fr19-bug097).
	curInstDecl *ast.FuncDecl
	substErr         error
	genericFuncDecls map[*types.Func]*ast.FuncDecl
	funcInsts        map[string]*funcInstWork
	funcInstQueue    []*funcInstWork
	monoCtxt         *types.Context
	// Method declarations on GENERIC types, keyed by the receiver's
	// ORIGIN named type: skipped by the declaration loop (a generic
	// method has no uninstantiated runtime form) and stenciled per
	// receiver instantiation (flushTypeInsts).
	genericMethodDecls map[*types.Named][]*ast.FuncDecl
	// Instantiated-type declarations: dedup map + pending queue of
	// TypeDef/method stencils, one per mangled TypeId that reaches the
	// wire (instTypeIdForWire).
	typeInsts     map[string]*typeInstWork
	typeInstQueue []*typeInstWork
	// Journal of every mono registration, for the per-decl quarantine
	// rollback (audit response m5; see rollbackMono).
	monoLog []monoLogEntry

	// Multi-package lowering (raft W1.1,
	// docs/2026-08-18_multipackage-identity.md): the source units in
	// PROGRAM INITIALIZATION ORDER (main last), and the set/main views
	// the qualification rules key on. Nil units = a directly
	// constructed single-package emitter (unit tests): every helper
	// falls back to the historic e.pkg-only semantics.
	units     []*sourcePkg
	mainPkg   *types.Package
	srcPkgSet map[*types.Package]*sourcePkg

	// Dotted import paths that reached a TypeId/FuncId qualifier: the
	// key GRAMMAR reserves '.' for the qualifier/name separator
	// (identity note §1/§3 — `TypeId.unqualified` and the injectivity
	// argument both depend on dot-free qualifiers), so
	// `checkKeyPathGrammar` fails the export closed when any is
	// recorded. Successor of the retired package-NAME collision check
	// (BUG-010: keys are path-qualified now, so distinct packages
	// cannot collide by construction).
	badKeyPaths map[string]string // path -> keyPathHazard reason

	// Package-level variables (init slice, docs/2026-08-05_init-design.md):
	// `collectGlobals` is the SINGLE place gids come from — a dense index
	// per package-scope *types.Var in declaration order (files in lexical
	// filename order), matching the driver's seeding of cell gid at
	// Loc.base(gid). Blank package-level vars have no cell and no gid
	// (their initializers still run via InitOrder). `globalInitStmt` maps
	// each initializer's RHS expression to a fabricated assignment whose
	// Lhs are the ORIGINAL declaring idents, so `$pkginit` synthesis
	// reuses the ordinary emitAssign machinery (hoists, interface boxing,
	// multi-value calls, blank targets). Init-function ids live
	// per-unit (`sourcePkg.initNames` — multi-package, W1.1).
	globalVars     map[*types.Var]int
	globalDefs     []any
	globalInitStmt map[ast.Expr]*ast.AssignStmt

	// H-11 (raft W4.0): per-declaration quarantine for package-level
	// vars whose initializer does not lower. The var KEEPS its
	// type-carrying globals entry (gid density, zero-seeding) but its
	// initializer is SKIPPED by $pkginit (`quarantinedInits`, keyed by
	// the initializer's RHS like globalInitStmt) and EVERY reference —
	// read, write, address-of, qualified or not — refuses at the
	// globalAddr choke point naming the var, so the zero in the cell is
	// unreachable, never a silent answer. Populated by
	// quarantineUnlowerableGlobals (the dry-run pre-pass) BEFORE any
	// function body is emitted — and, since FR-24 (2026-09-04), by
	// collectGlobals for a var whose TYPE does not lower (globalPoison
	// records which of the two it is; the refusal text differs).
	quarantinedGlobals map[*types.Var]globalPoison
	quarantinedInits   map[ast.Expr]bool

	// Stdlib source-through (stdlibsource.go / stdlibreach.go). curUnit
	// is the unit whose declarations are being emitted (setUnit); a
	// library unit's reachSet prunes its declaration passes. prunedInits
	// collects the initializer RHS expressions of UNREACHED library var
	// specs (skipped by the H-11 dry run and by $pkginit — their cells
	// are never allocated either). forcedQuarantine carries reached
	// library FuncDecls the pre-emission unsafe-layout scan condemned:
	// the FuncDecl loop stubs them (H-3) instead of emitting.
	curUnit          *sourcePkg
	prunedInits      map[ast.Expr]bool
	forcedQuarantine map[*ast.FuncDecl]string
}

// noteInterface records an interface type for the `interface` TypeDef pass.
// The canonical EMPTY interface (`any`) is excluded on purpose: it is
// satisfied by every type BY DESIGN in the machine (Go's `any`), so it needs
// no declaration — and keeping it off the wire keeps `any`-using programs'
// lowering unchanged.
// FIRST-time registrations are journaled for the quarantine rollback
// (delta-review R1): an interface noted only by a refused body must not
// survive into the declaration pass, whose failure (an unsupported
// method signature) refuses the WHOLE export. Re-notes of an existing
// name are not journaled, so a rollback never deletes an entry a
// SUCCESSFUL declaration also owns.
func (e *emitter) noteInterface(name string, iface *types.Interface) {
	if name == emptyInterfaceName {
		return
	}
	// Record the interface AT THE ACTIVE INSTANTIATION (arc-final audit
	// F5, 2026-08-06): the wire NAME is substitution-aware
	// (ifaceWireName), but a dispatch through a generic interface used
	// at the enclosing function's type parameter hands this the ORIGIN
	// interface, whose method signatures still mention T — the
	// declaration pass then emits them with curSubst cleared and refuses
	// the WHOLE export ("type parameter T outside an instantiation").
	// Substituting here keys the substituted method set under the
	// substituted name. applySubst is identity outside stenciling; a
	// substitution failure keeps the origin (fail-closed downstream).
	if e.curSubst != nil {
		savedErr := e.substErr
		if sub, ok := types.Unalias(e.applySubst(iface)).(*types.Interface); ok {
			iface = sub
		}
		// A failed attempt keeps the origin (the declaration pass then
		// refuses loudly on the unsubstituted signature, as before) and
		// must not poison substErr for unrelated emission.
		e.substErr = savedErr
	}
	if e.seenInterfaces == nil {
		e.seenInterfaces = map[string]*types.Interface{}
	}
	e.noteUnexportedRequirements(iface)
	if prev, seen := e.seenInterfaces[name]; seen {
		// Same name, different method set: recorded here, refused by
		// emitProgram's declaration pass (BUG-095: the dispatch sites used
		// to register a method's DECLARING interface under the STATIC
		// operand's name, and last-writer-wins silently shrank an embedding
		// interface's requirement list to the embedded subset).
		if !types.Identical(prev, iface) {
			e.ifaceConflicts = append(e.ifaceConflicts, fmt.Sprintf("%s (%s vs %s)", name,
				types.TypeString(prev, nil), types.TypeString(iface, nil)))
		}
		return
	}
	e.monoLog = append(e.monoLog, monoLogEntry{monoLogSeenIface, name})
	e.seenInterfaces[name] = iface
}

// ifaceConflictRefusal is the fail-closed half of BUG-095's fix: a wire
// name registered with two NON-IDENTICAL method sets (ifaceConflicts)
// refuses the export BY NAME. The list is deduplicated first — every
// re-registration of the same pair appends one more copy (once per
// dispatch site; audit fix R7, 2026-09-05) — and sorted, so the refusal
// text is deterministic and names each collision once.
func (e *emitter) ifaceConflictRefusal() error {
	if len(e.ifaceConflicts) == 0 {
		return nil
	}
	seen := map[string]bool{}
	uniq := make([]string, 0, len(e.ifaceConflicts))
	for _, c := range e.ifaceConflicts {
		if !seen[c] {
			seen[c] = true
			uniq = append(uniq, c)
		}
	}
	sort.Strings(uniq)
	return unsup("interface wire name registered with two different method sets: %s", strings.Join(uniq, "; "))
}

// staticIfaceOf resolves the *types.Interface a STATIC interface-typed
// operand denotes — alias-transparent and substitution-aware (a type
// parameter under stenciling resolves to its instantiation; an
// unsubstituted one is refused, its constraint being no value type). This
// is the interface whose FULL method set belongs under the operand's wire
// name. The method's declaring receiver (`Signature.Recv()`) is NOT it when
// the method is promoted from an embedded interface (BUG-095).
func (e *emitter) staticIfaceOf(t types.Type) (*types.Interface, bool) {
	t = types.Unalias(e.applySubst(t))
	if _, isTP := t.(*types.TypeParam); isTP {
		return nil, false
	}
	iface, ok := t.Underlying().(*types.Interface)
	return iface, ok
}

// noteCalledIfaceMethod records one interface-dispatch call target (the
// anchor-synthesis input), journaled like noteInterface (delta-review
// R1): a dispatch recorded only by a refused body must not force a
// synthesized anchor whose signature emission would refuse the export.
func (e *emitter) noteCalledIfaceMethod(key string, cm calledIfaceMethod) {
	if e.calledIfaceMethods == nil {
		e.calledIfaceMethods = map[string]calledIfaceMethod{}
	}
	if _, seen := e.calledIfaceMethods[key]; !seen {
		e.monoLog = append(e.monoLog, monoLogEntry{monoLogCalledIface, key})
	}
	e.calledIfaceMethods[key] = cm
}

// calledIfaceMethod records one interface-dispatch call target: the receiver
// interface's wire name (qualified, or bare for predeclared), the method
// name, and its signature (for params/results of a synthesized table entry).
type calledIfaceMethod struct {
	ifaceName string
	method    string
	sig       *types.Signature
	// The stencil substitution ACTIVE at the call site (nil outside an
	// instantiation). The recorded sig is the ORIGIN method's — for a
	// generic interface used at the enclosing function's type parameter
	// (`gipVisitor[T].Visit` inside `gipApply[T]`) it still mentions T,
	// while the KEY is substitution-aware; the anchor pass must emit the
	// signature under THIS substitution, not with curSubst cleared
	// (arc-final audit F5, 2026-08-06: the un-substituted emission
	// refused the WHOLE export with "type parameter T outside an
	// instantiation", poisoning unrelated subjects in the package).
	subst map[*types.TypeParam]types.Type
}

// emptyStructName is the canonical GoCore type name for the empty struct
// struct{} (the set-value idiom map[K]struct{}).
const emptyStructName = "struct{}"

// emptyInterfaceName is the canonical GoCore type name for the empty interface
// (`any` / `interface{}`) — the one interface the machine satisfies by design.
const emptyInterfaceName = "any"

// unsupported is returned when a construct is not yet modeled. The pipeline
// fails closed: the emitter never approximates.
type unsupported struct{ what string }

func (u unsupported) Error() string { return "native frontend unsupported: " + u.what }

func unsup(format string, args ...any) error {
	return unsupported{fmt.Sprintf(format, args...)}
}

// ---- types ----

func (e *emitter) emitType(t types.Type) (any, error) {
	// The single type choke point applies the ACTIVE stencil substitution
	// (mono.go): every wire type inside a stencil is emitted at the
	// current instantiation. Identity outside stenciling.
	if e.curSubst != nil {
		t = e.applySubst(t)
	}
	switch ty := t.(type) {
	case *types.Basic:
		if ty.Kind() == types.Invalid && e.substErr != nil {
			// applySubst surfaced a substitution failure as Invalid;
			// report the recorded cause, not a generic message.
			return nil, e.substErr
		}
		return e.emitBasic(ty)
	case *types.Alias:
		// Aliases — generic ones included (gotypesalias=1, G4) — are
		// IDENTITY-TRANSPARENT (spec §Alias declarations; design-note
		// §3.2 "aliases never mint TypeIds"): the wire sees the aliased
		// type directly, e.g. aliasSlice[int] emits as []int.
		return e.emitType(types.Unalias(ty))
	case *types.TypeParam:
		// Reachable only OUTSIDE a stencil (inside one, applySubst above
		// either resolves it or records substErr): a generic declaration
		// being emitted un-instantiated — fail closed (this is also the
		// per-decl quarantine trigger for generic declarations).
		return nil, unsup("type parameter %s outside an instantiation", ty)
	case *types.Named:
		// sync/atomic types (atomics arc wave 1, atomics.go): the five
		// typed INTEGER wrappers ride the E5-T shadow model through the
		// ordinary imported-named path below (their identity is
		// recorded in importedNamed and the model's real TypeDef +
		// method bodies are harvested in emitProgram); Value/Bool/
		// Pointer[T] REFUSE here with their wave-2 cause, so the red
		// lands at frontend-export by name, never as a dangling stub
		// whose call refuses downstream. The check runs BEFORE the
		// instantiated-named arm because Pointer[T] is generic.
		if o := ty.Obj(); o.Pkg() != nil && o.Pkg().Path() == atomicPkgPath && !e.isSourcePackage(o.Pkg()) {
			if cause, wave2 := atomicWave2Types[o.Name()]; wave2 {
				return nil, unsup("sync/atomic.%s: %s", o.Name(), cause)
			}
			if !atomicTypedWrappers[o.Name()] {
				return nil, unsup("sync/atomic.%s (outside the modeled sync/atomic surface — wave 1 models the typed integer wrappers Int32/Int64/Uint32/Uint64/Uintptr)", o.Name())
			}
		}
		if ty.TypeArgs().Len() > 0 {
			return e.emitInstantiatedNamed(ty)
		}
		obj := ty.Obj()
		// Sync primitive types (spec-parity slice 2, design note §7):
		// exactly the four in-scope kinds map to machine sync types
		// (zero value = the ready primitive). Each is REGISTERED for
		// the method-set stub pass (arc-end fix round 2026-08-10): the
		// old early return skipped every method-table registration, so
		// satisfaction against a bare `*sync.Mutex` answered a false
		// "no" — wrong comma-ok bool, wrong type-switch branch, and a
		// fabricated missing-method panic, all with status ok.
		// sync.Locker is a PLAIN INTERFACE (Lock/Unlock) and rides the
		// general named-interface path below — needed both for its own
		// satisfaction/boxing and for RLocker's result signature.
		// Every OTHER sync.* type fails closed here (per-decl
		// quarantine upstream).
		if obj.Pkg() != nil && obj.Pkg().Path() == "sync" && obj.Name() != "Locker" {
			switch obj.Name() {
			case "Mutex", "RWMutex", "WaitGroup", "Once":
				if e.syncUsed == nil {
					e.syncUsed = map[string]*types.Named{}
				}
				e.syncUsed[obj.Name()] = ty
				return map[string]any{"kind": "sync", "sync": obj.Name()}, nil
			default:
				return nil, unsup("sync.%s (only Mutex/RWMutex/WaitGroup/Once are modeled)", obj.Name())
			}
		}
		// A named type whose underlying is an interface is an interface type;
		// otherwise it is a defined type. GoCore distinguishes the two. Names
		// are package-qualified ("main.T"); predeclared types (error) stay
		// bare (no package).
		if iface, ok := ty.Underlying().(*types.Interface); ok {
			name := e.qualifiedTypeName(obj)
			e.noteInterface(name, iface)
			return map[string]any{"kind": "interface", "name": name}, nil
		}
		qname := e.qualifiedTypeName(obj)
		if obj.Pkg() != nil && (!e.isSourcePackage(obj.Pkg()) || (e.isLibraryPackage(obj.Pkg()) && modeledImportedTypes[qname] != nil)) {
			// An imported concrete named type OUTSIDE the source
			// program (stdlib): record it for the method-set stub pass
			// (D5). Source-package types get REAL TypeDefs from their
			// own unit's declaration pass (multi-package, W1.1) — EXCEPT
			// the E5-T shadow-modeled types (importedmodel.go): when
			// their package is loaded as a stdlib source-through
			// LIBRARY unit (stdlibsource.go), the shadow model stays the
			// declaration of record until slice 2's overlay (the real
			// `strings.Builder` needs unsafe.String), so they register
			// here exactly as before and the library unit's declaration
			// pass never reaches them (stdlibreach.go stops at them).
			if e.importedNamed == nil {
				e.importedNamed = map[string]*types.Named{}
			}
			if _, seen := e.importedNamed[qname]; !seen {
				// Journaled so a refused body's registration rolls back
				// with the body (rollbackMono, monoLogImportedNamed).
				e.monoLog = append(e.monoLog, monoLogEntry{monoLogImportedNamed, qname})
			}
			e.importedNamed[qname] = ty
		}
		return map[string]any{"kind": "named", "name": qname}, nil
	case *types.Pointer:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "pointer", "elem": elem}, nil
	case *types.Slice:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "slice", "elem": elem}, nil
	case *types.Array:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "array", "len": ty.Len(), "elem": elem}, nil
	case *types.Map:
		key, err := e.emitType(ty.Key())
		if err != nil {
			return nil, err
		}
		val, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "map", "key": key, "value": val}, nil
	case *types.Chan:
		// Direction is a static type property and part of type IDENTITY
		// (channels arc slice 1): carried on the wire type verbatim.
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		dir := "both"
		switch ty.Dir() {
		case types.SendOnly:
			dir = "send"
		case types.RecvOnly:
			dir = "recv"
		}
		return map[string]any{"kind": "chan", "dir": dir, "elem": elem}, nil
	case *types.Interface:
		if ty.Empty() {
			return map[string]any{"kind": "interface", "name": emptyInterfaceName}, nil
		}
		// Anonymous non-empty interface (a `case interface{ M() }`, an
		// assert target, a variable type): canonical wire name from the
		// type's own IDENTITY rendering — SOUND because Go interface
		// identity is structural, so structurally identical method sets
		// are one type (design note 2026-08-05 D3). The key is minted by
		// the ONE constructor anonIfaceKey (identity.go; BUG-097 fixed
		// 2026-09-05): path-qualified named types, path-qualified
		// unexported method names, scope-ordinal local types — so two
		// same-named packages' `interface{ Get() T }` are two keys and
		// noteInterface's BUG-095 conflict guard never sees them as one.
		// The gc display (`interface { Get() inner.T }`) travels
		// separately (design note §3). Registered like named interfaces,
		// so the declaration pass emits its full method set.
		name, err := e.anonIfaceKey(ty)
		if err != nil {
			return nil, err
		}
		e.noteInterface(name, ty)
		return map[string]any{"kind": "interface", "name": name}, nil
	case *types.Signature:
		params := []any{}
		for i := 0; i < ty.Params().Len(); i++ {
			pt, err := e.emitType(ty.Params().At(i).Type())
			if err != nil {
				return nil, err
			}
			params = append(params, pt)
		}
		results := []any{}
		for i := 0; i < ty.Results().Len(); i++ {
			rt, err := e.emitType(ty.Results().At(i).Type())
			if err != nil {
				return nil, err
			}
			results = append(results, rt)
		}
		// `variadic` is part of func TYPE IDENTITY (spec#Type_identity:
		// "either both functions are variadic or neither is") — go/types
		// types the variadic parameter []T, so without this bit
		// `func(...int)` and `func([]int)` collapsed to one wire node and
		// a comma-ok assert answered true for both where gc distinguishes
		// (BUG-067, census H-d). Func declarations and interface-method
		// requirements always carried it (finding 0); the TYPE node is
		// the third leg.
		return map[string]any{"kind": "func", "params": params, "results": results,
			"variadic": ty.Variadic()}, nil
	case *types.Struct:
		// The empty struct struct{} (the set-value idiom map[K]struct{}) is a
		// canonical named empty struct in GoCore; other anonymous structs are
		// not modeled.
		if ty.NumFields() == 0 {
			return map[string]any{"kind": "named", "name": emptyStructName}, nil
		}
		return nil, unsup("anonymous non-empty struct type %s", ty)
	case *types.Tuple:
		// A tuple is never a type a Go program can name — it reaches
		// here only when a lowering hoists a MULTI-VALUE expression
		// whole (e.g. the shadow-capture pre-bind of a comma-ok
		// initializer, triage F22 / mini-slice A5). Name the construct,
		// not the go/types internal (audit fix round F-B3: the old
		// catch-all printed "type *types.Tuple ((int, bool))").
		return nil, unsup("multi-value expression hoisted as a single value (%s) — no tuple type exists on the wire", ty)
	default:
		return nil, unsup("type %T (%s)", t, t)
	}
}

func (e *emitter) emitBasic(b *types.Basic) (any, error) {
	switch b.Kind() {
	case types.Bool:
		return map[string]any{"kind": "bool"}, nil
	case types.String:
		return map[string]any{"kind": "string"}, nil
	case types.Int:
		return intType("int"), nil
	case types.Int8:
		return intType("int8"), nil
	case types.Int16:
		return intType("int16"), nil
	case types.Int32:
		return intType("int32"), nil
	case types.Int64:
		return intType("int64"), nil
	case types.Uint:
		return intType("uint"), nil
	case types.Uint8:
		return intType("uint8"), nil
	case types.Uint16:
		return intType("uint16"), nil
	case types.Uint32:
		return intType("uint32"), nil
	case types.Uint64:
		return intType("uint64"), nil
	case types.Uintptr:
		return intType("uintptr"), nil
	case types.Float32:
		return floatType("float32"), nil
	case types.Float64:
		return floatType("float64"), nil
	// Untyped constants carry their default type at use sites; go/types has
	// usually already resolved them, but guard the bare kinds.
	case types.UntypedInt:
		return intType("int"), nil
	case types.UntypedFloat:
		// The spec's default type for an untyped float constant.
		return floatType("float64"), nil
	case types.UntypedBool:
		return map[string]any{"kind": "bool"}, nil
	case types.UntypedString:
		return map[string]any{"kind": "string"}, nil
	default:
		// FR-25: in SIGNATURE-OPAQUE mode an unlowerable basic type is an
		// opaque marker (doc comment at opaqueBasics); everywhere else it
		// refuses — the FR-15 text the ledger row cites, unchanged.
		if e.sigOpaque {
			if key, cause, ok := opaqueBasicMarker(b); ok {
				if e.opaqueBasics == nil {
					e.opaqueBasics = map[string]*types.Basic{}
				}
				e.opaqueBasics[key] = b
				// A basic type's gc display is its own spelling.
				e.noteTypeDisplay(key, typeDisplay{display: key})
				if e.opaqueTouchedBasics == nil {
					e.opaqueTouchedBasics = map[string]bool{}
				}
				e.opaqueTouchedBasics[key] = true
				_ = cause // rendered by opaqueMarkerTypeDefs / opaqueSigClauses
				return map[string]any{"kind": "named", "name": key}, nil
			}
		}
		return nil, unsup("basic type %s", b)
	}
}

// opaqueBasicMarker names the basic kinds FR-25 carries as opaque markers
// in declaration signatures, with the cause the marker's TypeDef and the
// stub's reason state. Exactly the kinds emitBasic refuses that a
// SIGNATURE can mention: the untyped kinds exist only for constants and
// Invalid is an internal error, so both stay refusals (never masked).
func opaqueBasicMarker(b *types.Basic) (key, cause string, ok bool) {
	switch b.Kind() {
	case types.Complex64, types.Complex128:
		return b.String(), "not modeled (FR-15: complex numbers — the one large arc, last in the queue)", true
	case types.UnsafePointer:
		return b.String(), "out of language (package unsafe: implementation-specific layout, ledger §2 Package_unsafe)", true
	}
	return "", "", false
}

func intType(kind string) map[string]any {
	return map[string]any{"kind": "int", "int": kind}
}

func floatType(kind string) map[string]any {
	return map[string]any{"kind": "float", "float": kind}
}

// emitInstantiatedNamed is the wire arm for INSTANTIATED generic named
// types (mono.go): the type names by its mangled key, and its TypeDef —
// with the full stenciled method set — is enqueued for emission from the
// instantiation worklist. Instantiated INTERFACES need no TypeDef stencil
// of their own: go/types' instance Underlying() carries the substituted
// method set, and the seenInterfaces declaration pass emits it like any
// other interface (satisfaction requirements), with dispatch anchors
// synthesized from recorded calls.
func (e *emitter) emitInstantiatedNamed(ty *types.Named) (any, error) {
	if mentionsTypeParam(ty, nil) {
		return nil, unsup("instantiated type %s still mentions a type parameter", ty)
	}
	if e.sigOpaque {
		if obj := ty.Obj(); obj.Pkg() == nil || !e.isSourcePackage(obj.Pkg()) {
			// FR-23: an imported generic instantiation in a SIGNATURE
			// that never gets a body. The mangled key is the identity
			// (collision-registered like any instantiation); the marker
			// TypeDef is emitted from opaqueInsts in emitProgram. No
			// stencil is enqueued — there is no source to stencil from,
			// which is exactly why bodies refuse (enqueueTypeInst).
			key, err := e.instTypeId(ty)
			if err != nil {
				return nil, err
			}
			// The marker carries NO method stubs, so it is honest only for
			// a type whose exported method set is EMPTY (iter.Seq/Seq2 are
			// func types): a marker for `unique.Handle[T]` (has Value())
			// would make satisfaction answer a false "no" — the D5
			// skip-whole hazard. Refuse those (audit fix round, item 7).
			if ms := types.NewMethodSet(types.NewPointer(ty)); ms.Len() > 0 {
				exported := []string{}
				for i := 0; i < ms.Len(); i++ {
					if ms.At(i).Obj().Exported() {
						exported = append(exported, ms.At(i).Obj().Name())
					}
				}
				if len(exported) > 0 {
					return nil, unsup("instantiation of imported generic type %s in a declaration signature: the type has exported methods (%s) and the opaque marker carries no method stubs, so satisfaction could answer a false no — refused (FR-23 covers method-less imported generics only)", key, strings.Join(exported, ", "))
				}
			}
			if e.opaqueInsts == nil {
				e.opaqueInsts = map[string]*types.Named{}
			}
			e.opaqueInsts[key] = ty
			if e.opaqueTouchedInsts == nil {
				e.opaqueTouchedInsts = map[string]bool{}
			}
			e.opaqueTouchedInsts[key] = true
			return map[string]any{"kind": "named", "name": key}, nil
		}
	}
	if iface, isIface := ty.Underlying().(*types.Interface); isIface {
		if !iface.IsMethodSet() {
			return nil, unsup("constraint interface %s used as a value type", ty)
		}
		key, err := e.instTypeId(ty)
		if err != nil {
			return nil, err
		}
		e.noteInterface(key, iface)
		return map[string]any{"kind": "interface", "name": key}, nil
	}
	key, err := e.instTypeIdForWire(ty)
	if err != nil {
		return nil, err
	}
	return map[string]any{"kind": "named", "name": key}, nil
}

// typeOf returns the emitted wire type of an expression from go/types.
func (e *emitter) typeOf(expr ast.Expr) (any, error) {
	tv, ok := e.info.Types[expr]
	if !ok {
		if id, isID := expr.(*ast.Ident); isID {
			if obj := e.info.ObjectOf(id); obj != nil {
				return e.emitType(obj.Type())
			}
		}
		return nil, unsup("no type for expression %T at %s", expr, e.fset.Position(expr.Pos()))
	}
	return e.emitType(tv.Type)
}

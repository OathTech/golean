// Stdlib selector-call shims — extension E5 (gallery campaign G2,
// 2026-08-15; fidelity argument: docs/gallery-campaign-log/g2.md,
// "E5 — THE FIDELITY ARGUMENT").
//
// The machine has no standard library and must not grow one: a stdlib
// function modeled as a GoCore node would put LIBRARY behaviour inside
// the semantic core, where only Go LANGUAGE semantics belongs. An E5
// shim is frontend-maintained lowering code in the quarantine zone: a
// Go-SOURCE function, written in the already-modeled subset, injected
// into the user's package as a synthetic file before type-check
// whenever an allowlisted call shape (`strings.Fields(x)`) occurs;
// exactly those call sites are then emitted as ordinary static calls
// to the injected function (emit.go, emitStdlibShimCall). The shim
// lowers through the SAME pipeline as user code, so a consumer's
// golden pin records its lowered body verbatim.
//
// THE VALIDATION STORY: `go run` executes the REAL stdlib; the machine
// executes the shim. Every differential corpus row whose control flow
// crosses a shimmed call is therefore a direct oracle test of shim
// fidelity — the corpus is the shim's conformance suite
// (`strings/fields-conformance/*` is the dedicated slice, tag
// `stdlib`).
//
// FAIL-CLOSED RULES:
//   - The allowlist below is the whole scope. Every other selector
//     call keeps the standing per-declaration quarantine verbatim
//     ("selector call <Fn> is not a method value"). Widening the list
//     owes new guardrail corpus rows and a fidelity argument FIRST.
//   - Only the direct CALL shape `pkg.Fn(args)` is admitted. The
//     function VALUE (`f := strings.Fields`) and every other selector
//     reference shape keep their existing refusals. DOT IMPORTS ARE
//     THE EXCEPTION, and it is a PRE-EXISTING DEFECT, not a refusal:
//     `import . "strings"; Fields(x)` never reaches the selector
//     quarantine at all — it emits a dangling plain call and the
//     machine answers `stuck` ("GoCore function not found: Fields").
//     Visible-red, never a wrong answer, but a `stuck` where the
//     fail-closed doctrine wants an explicit boundary refusal. E5
//     neither widened nor narrowed it. Recorded in
//     docs/gallery-campaign-log/g2.md (findings); the clean fix is a
//     frontend refusal on `*types.Func` callees whose package is not
//     the user package. [Wording corrected 2026-08-16 by the
//     post-autonomy audit, which found this comment claiming a
//     refusal that does not exist.]
//   - Shim declaration names are reserved: a user package-level
//     declaration of the same name refuses the export loudly at
//     injection (never a silent merge or override).
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"sort"
)

// RETIRED SHIMS (stdlib source-through slice 1, 2026-09-03; memo
// docs/2026-09-03_stdlib-boundary-design.md §3 rows 1, 3, 4, 8, 9, 10 —
// G9 ruled AS RECOMMENDED by the [USER], relayed): strings.Fields,
// strings.Split, strings.TrimSpace, strconv.FormatUint, strconv.FormatInt
// AND strconv.ParseUint no longer have injected sources; their calls
// lower as qualified calls into the REAL library units loaded from the
// pinned GOROOT (stdlibsource.go). ParseUint's upstream error path
// reaches internal/stringslite.Clone's `unsafe.String` (a site the
// memo's §1.3 census did not list), so its error-path rows are DESIGNED
// REDS pending the slice-2 overlay — BUG-089; the alternative (a
// re-bodied shim constructing the real *strconv.NumError, which needed
// a shim→library import coupling) was posed as a D-002 exception and
// DENIED by the [USER] (Mike, 2026-09-03, relayed: «we're not running
// Raft right now, I think going red is simpler and safer, and lets us do
// a clean retirement»). The freeze is intact: no shim body changed.
//
// RETIRED SHIMS (stdlib source-through slice 2 `stdlib-source-2`,
// 2026-09-03; memo §3 rows 2, 5, 6, 7, 11–14, T1, T2): strings.Join,
// strings.Repeat, errors.New (the USER-FACING call), bytes.Equal,
// binary.LittleEndian.{Uint64,PutUint64} (the package-variable method
// desugar, fmtdesugar.go), slices.SortFunc (the generic desugar,
// genericshim.go — file deleted), and the two E5-T shadow types
// strings.Builder / bytes.Buffer (importedmodel.go) lower from the pinned
// GOROOT text — `strings`, `bytes`, `slices`, `cmp`, `encoding/binary`
// are source-through units; the `unsafe` idioms inside strings.Builder,
// errors.Join and internal/stringslite.Clone are OVERLAID (stdlib-
// overlay.tsv, byte-checked, cap 12). cmp.Compare's kind-dispatch
// desugar, RETAINED by slice 2's STOP rule, was RETIRED 2026-09-04 (lane
// fr24) per the [USER] ruling «(2) given we have a plan, I think this
// should be an honest red» (relayed by the coordinator): cmpshim.go is
// deleted and slices/sortfunc-cmp/cmp-compare-kinds is red on FR-19's
// line (mono.go's function-local-type naming refusal, C6).
// What remains here is the fmt DESUGAR bundle (memo §2.3.3 / G5 —
// slice 4 re-homes it) and, inside it, goleanShimErrorsNew as fmt.Errorf's error constructor ONLY: a user
// `errors.New(...)` is the real library function now; Errorf's constructed
// error keeps the injected type until slice 4 routes Errorf onto the real
// errors.New (recorded delta: `*main.goleanShimErrorString` vs
// `*errors.errorString`, unobservable without errors.Is/As — G6).

// errorsNewShimName / errorsNewShimTypeName are the reserved
// declaration names of the errors.New shim (raft W4.0, G-2/H-10). The
// shim is TWO declarations — the constructor and its unexported
// concrete type — so both names are reserved (stdlibShimDeclNames).
const errorsNewShimName = "goleanShimErrorsNew"
const errorsNewShimTypeName = "goleanShimErrorString"

// fmtShimBundleKey: the fmt DESUGAR bundle (raft W4.1 item 2, H-6 —
// fmtdesugar.go). fmt.{Sprintf,Errorf,Fprintf} are NOT direct-call
// shims: the emitter parses the constant format string and desugars per
// verb; the bundle injects the per-verb helper functions those desugars
// call. Stringer/error rendering takes the CONCRETE method VALUE (a
// func() string parameter), never an interface dispatch — which is both
// fmt-faithful (the dynamic type is the static one at every modeled
// site) and what keeps the reachability instruments PRECISE (an
// interface dispatch edge inside a shim would mark every String method
// in the program a live candidate — measured on the raft tree before
// this shape was chosen, docs/raft-w41-log.md item 2). Keyed by the
// first helper's name.
const fmtShimBundleKey = "goleanShimFmtUint"

// fmtDynShimKey: the DYNAMIC fmt bundle (W4.3 item 1 landing C —
// cause 9): Sprintf/Sprint/Sprintln with a SPREAD []any argument
// desugar to runtime-formatter shims (fmtdesugar.go's dyn route). The
// dyn helpers call the static bundle's renderers, so the injection
// rows below co-inject both bundles.
const fmtDynShimKey = "goleanShimFmtSprintfDyn"

// shimUnsupportedName (audit R4-C-3): the one helper every golean
// RUNTIME refusal routes through. Its DECLARATION is force-quarantined
// by the emitter (emitFuncDecl special-cases the name), so a call to
// it throws GoError.unsupported — an interpreter-level stop that user
// recover() CANNOT catch (a StepFn `throw` never enters the
// .panicking machinery). As plain `panic("golean ...")`s these
// refusals were RECOVERABLE, and ordinary defensive idioms (recover
// around a parse; fmt's own recover around a user String()) turned
// them into silent wrong answers — probe r4-p2, rows
// panic-recover/shim-refusal-unrecoverable. UPSTREAM-FAITHFUL panics
// (strconv illegal-base, strings negative-Repeat, the b[7] bounds
// shapes) stay ordinary panics: gc panics there too, and recover MUST
// catch them. Injected whenever any shim is (it costs one dead decl).
const shimUnsupportedName = "goleanShimUnsupported"


// stdlibShimAllowlist: package import path -> selector name -> shim
// declaration name for DIRECT-CALL shims. EMPTY since slice 2 (every
// direct-call shim is retired onto source-through); kept as the table
// the emitter (emitStdlibShimCall), the reach walk and the register
// consult, so a future entry has exactly one place to land — and lands
// against the register's frozen count.
var stdlibShimAllowlist = map[string]map[string]string{}

// stdlibGenericDesugarInject: packages whose GENERIC members desugared at
// emit time — the injection scan plants their shims on call presence,
// like stdlibDesugarInject, for a call that is not a direct-call rewrite.
// EMPTY since 2026-09-04 (lane fr24): the last entry, cmp.Compare's
// kind-dispatch desugar (cmpshim.go, deleted), was RETIRED per the [USER]
// ruling (Mike 2026-09-04, relayed by the coordinator, cited as relayed:
// «(2) given we have a plan, I think this should be an honest red») —
// cmp.Compare is the real source-through generic at EVERY type argument;
// a function-local defined type argument refuses at mono.go's C6 naming
// rule (row slices/sortfunc-cmp/cmp-compare-kinds, red on FR-19's line).
// Kept as the table the emitter, the reach walk and the register consult,
// so a future entry has exactly one place to land — against the
// register's frozen count.
var stdlibGenericDesugarInject = map[string]map[string][]string{}

// stdlibDesugarInject: package import path -> selector names whose
// CALL presence triggers a shim-bundle injection although the call
// itself is DESUGARED rather than rewritten to a direct shim call
// (fmtdesugar.go). The fmt bundle co-injects the errors.New shim:
// fmt.Errorf desugars to goleanShimErrorsNew over the formatted text.
var stdlibDesugarInject = map[string]map[string][]string{
	"fmt": {
		"Sprintf":  {fmtShimBundleKey, fmtDynShimKey},
		"Errorf":   {fmtShimBundleKey, errorsNewShimName},
		"Fprintf":  {fmtShimBundleKey},
		"Fprint":   {fmtShimBundleKey},
		"Sprint":   {fmtShimBundleKey, fmtDynShimKey},
		"Sprintln": {fmtShimBundleKey, fmtDynShimKey},
	},
}

// stdlibShimDeclNames: every RESERVED top-level name a shim injects,
// keyed by the shim's key declaration name. The collision check ranges
// over all of them — a user declaration matching ANY injected name
// refuses the export loudly (never a silent merge). Methods on shim
// types need no row: declaring one requires naming the receiver type,
// which is itself reserved here.
var stdlibShimDeclNames = map[string][]string{
	errorsNewShimName: {errorsNewShimName, errorsNewShimTypeName},
	fmtShimBundleKey: {fmtShimBundleKey, "goleanShimFmtInt", "goleanShimFmtHex",
		"goleanShimFmtBool", "goleanShimFmtQuoteBytes", "goleanShimFmtQuoteString",
		"goleanShimFmtStringVerb", "goleanShimFmtHexString", "goleanShimFmtRender",
		"goleanShimFmtRenderCall", "goleanShimFmtError", "goleanShimFmtErrorCall",
		"goleanShimFmtPanicValue", "goleanShimFmtIntPad", "goleanShimFmtUintPad",
		"goleanShimFmtPadLeft"},
	fmtDynShimKey: {fmtDynShimKey, "goleanShimStringer",
		"goleanShimFmtDynVerb", "goleanShimFmtDynInt", "goleanShimFmtDynUint",
		"goleanShimFmtSprintDyn", "goleanShimFmtSprintlnDyn"},
	shimUnsupportedName:      {shimUnsupportedName},
}

// stdlibShimDeps: shim key -> the OTHER shim keys whose sources its
// own source calls. The injection scan marks the shims the program's
// call sites map to; closeShimDeps then adds these transitively, so a
// planted bundle is always closed under its own references (BUG-086:
// a FormatInt-only program planted FormatInt's source, which calls
// goleanShimStrconvFormatUint, without the FormatUint shim — and the
// export died in the type-checker). This table is a property of the
// shim SOURCES, not of any call-site row, so it is declared once here
// and CHECKED against the sources by stdlibshim_closure_test.go in
// both directions (a reference with no row here, or a row with no
// reference, fails the build's tests). shimUnsupportedName is never
// listed: it rides along with every bundle (injectStdlibShims).
// D-002: plumbing only — no shim, no body, no allowlist row changes.
var stdlibShimDeps = map[string][]string{
	fmtDynShimKey: {fmtShimBundleKey},
}

// closeShimDeps adds to needed, transitively, every shim a needed
// shim's source depends on (stdlibShimDeps). Fails closed on a
// dependency that names no shim source: a typo in the table must
// refuse the export, never plant an empty string.
func closeShimDeps(needed map[string]bool) error {
	work := make([]string, 0, len(needed))
	for shim := range needed {
		work = append(work, shim)
	}
	for len(work) > 0 {
		shim := work[len(work)-1]
		work = work[:len(work)-1]
		for _, dep := range stdlibShimDeps[shim] {
			if _, ok := stdlibShimSources[dep]; !ok {
				return fmt.Errorf("internal: stdlib shim %s depends on %s, which has no shim source (stdlibShimDeps)", shim, dep)
			}
			if !needed[dep] {
				needed[dep] = true
				work = append(work, dep)
			}
		}
	}
	return nil
}

// shimRuntimeRefusalReasons: reserved helper name -> the quarantine
// reason its FORCE-QUARANTINED wire declaration carries (emit.go,
// emitFuncDecl). Calling one throws GoError.unsupported with exactly
// this text — the unrecoverable R4-C-3 stop. (The cause-named
// strings.Repeat bound helper of t1-fidelity-fixes left with the Repeat
// shim in slice 2: the real strings.Repeat has no golean bound — an
// output the machine cannot materialize refuses through the BUG-078
// allocation budget, by name.)
var shimRuntimeRefusalReasons = map[string]string{
	shimUnsupportedName: "golean stdlib shim RUNTIME refusal (fail closed): a modeled member hit a recorded bound at run time — the bound's text is at the shim call site. Unrecoverable BY DESIGN (audit R4-C-3): as a Go panic this was catchable, and user recover() turned refusals into silent wrong answers",
}

// stdlibShimSources: shim declaration name -> Go source of the
// injected declaration. Each shim body must stay inside the modeled
// subset (it lowers through the ordinary pipeline) and must be
// semantically equal to the stdlib function it stands for — the
// fidelity argument for THIS body, including the 600k-trial
// shim-vs-stdlib fuzz and the byte-scan-equals-rune-scan argument, is
// the g2.md E5 section; the conformance rows pin it differentially
// forever after.
var stdlibShimSources = map[string]string{

	// errors.New: "returns an error that formats as the given text.
	// Each call to New returns a distinct error value even if the text
	// is identical."
	//
	// The body is BYTE-EQUIVALENT to go/src/errors/errors.go's
	// New/errorString modulo names (upstream: `return &errorString{text}`;
	// the field is keyed here for readability, same composite). The
	// fidelity argument (raft W4.0, docs/raft-w4-log.md item 2), in
	// full:
	//   - IDENTITY: `==` on error values compares (dynamic type,
	//     dynamic value); the dynamic value is a fresh *T per call
	//     (nonzero-size allocations are distinct — probed against
	//     go1.26.5: two News of equal text are !=, self-== holds,
	//     sentinel identity survives helper returns), so freshness and
	//     sentinel discrimination are inherited from the machine's
	//     allocator, not asserted. A shim that interned by text would
	//     silently make every same-text comparison true (raft branches
	//     on `err == errBreak` — W3 log §2.4).
	//   - NIL-NESS: the shim returns a non-nil interface always, as
	//     upstream does.
	//   - Error(): returns the constructor's string verbatim.
	//   - THE ONE DELTA: the dynamic type NAME (*errors.errorString
	//     upstream vs *<pkg>.goleanShimErrorString here, one type PER
	//     INJECTED PACKAGE where upstream has one total). Unobservable
	//     in the modeled subset: user code cannot name the unexported
	//     upstream type (no assertion/type-switch can target it), fmt
	//     verbs and reflection are not modeled (they refuse), and the
	//     type component of `==` cannot flip an answer — values from
	//     different calls are distinct pointers (both sides false
	//     regardless of type), values from the same call are identical
	//     in both components.
	errorsNewShimName: `
// goleanShimErrorString / goleanShimErrorsNew are the native frontend's
// errors.New shim (extension E5, raft W4.0). Injected declarations —
// not user code. See tools/nativefrontend/stdlibshim.go for the
// contract and docs/raft-w4-log.md item 2 for the fidelity argument.
type goleanShimErrorString struct{ s string }

func (e *goleanShimErrorString) Error() string { return e.s }

func goleanShimErrorsNew(text string) error {
	return &goleanShimErrorString{s: text}
}
`,

	// The fmt DESUGAR bundle (raft W4.1 item 2, H-6 — see fmtdesugar.go
	// for the modeled matrix and the fidelity bounds; every behavior
	// below is probed against gc and pinned by fmt/sprintf-verbs):
	//   - decimal/hex digit loops (no strconv);
	//   - the ASCII %q quoter (fails closed on bytes >= 0x80, where the
	//     real %q prints printable non-ASCII runes literally);
	//   - the Stringer/error renderers (the render helper takes the
	//     CONCRETE method value — see fmtShimBundleKey's comment), with
	//     fmt's recover-and-render:
	//     panic value rendered after "String method: "/"Error method: "
	//     under "%!<verb>(PANIC=...)" (verb WITHOUT flags), a panicking
	//     NIL-POINTER receiver rendering "<nil>", a nil error interface
	//     rendering "<nil>" for %v and "%!s(<nil>)" for %s. A panic
	//     value that is neither string nor error, or a nested panic,
	//     fails closed by re-panicking (fmt would nest-render; the
	//     subject's stubs panic with string literals).
	//   - the VERB post-process on a method result
	//     (goleanShimFmtStringVerb): %x hexes it, %q quotes it, %s/%v
	//     pass it through — gc hands the String()/Error() result to the
	//     same code that formats a plain string. It runs OUTSIDE the
	//     recover frame on purpose (audit A-F1): the PANIC render must
	//     not be post-processed, and %q's fail-closed non-ASCII panic
	//     must PROPAGATE rather than be caught and mis-rendered as a
	//     String-method panic.
	fmtShimBundleKey: `
// goleanShimFmt* are the native frontend's fmt-desugar helpers
// (raft W4.1 item 2). Injected declarations — not user code. See
// tools/nativefrontend/fmtdesugar.go for the contract.
func goleanShimFmtUint(v uint64) string {
	if v == 0 {
		return "0"
	}
	digits := []byte{}
	for v > 0 {
		digits = append(digits, byte('0'+v%10))
		v /= 10
	}
	out := []byte{}
	for i := len(digits) - 1; i >= 0; i-- {
		out = append(out, digits[i])
	}
	return string(out)
}

func goleanShimFmtInt(v int64) string {
	if v < 0 {
		return "-" + goleanShimFmtUint(^uint64(v)+1)
	}
	return goleanShimFmtUint(uint64(v))
}

func goleanShimFmtHex(v uint64) string {
	if v == 0 {
		return "0"
	}
	hexits := "0123456789abcdef"
	digits := []byte{}
	for v > 0 {
		digits = append(digits, hexits[v&0xf])
		v >>= 4
	}
	out := []byte{}
	for i := len(digits) - 1; i >= 0; i-- {
		out = append(out, digits[i])
	}
	return string(out)
}

func goleanShimFmtBool(v bool) string {
	if v {
		return "true"
	}
	return "false"
}

func goleanShimFmtQuoteBytes(b []byte) string {
	return goleanShimFmtQuoteString(string(b))
}

func goleanShimFmtQuoteString(s string) string {
	hexits := "0123456789abcdef"
	out := []byte{'"'}
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '"':
			out = append(out, '\\', '"')
		case c == '\\':
			out = append(out, '\\', '\\')
		case c == '\a':
			out = append(out, '\\', 'a')
		case c == '\b':
			out = append(out, '\\', 'b')
		case c == '\f':
			out = append(out, '\\', 'f')
		case c == '\n':
			out = append(out, '\\', 'n')
		case c == '\r':
			out = append(out, '\\', 'r')
		case c == '\t':
			out = append(out, '\\', 't')
		case c == '\v':
			out = append(out, '\\', 'v')
		case c >= 0x20 && c < 0x7f:
			out = append(out, c)
		case c < 0x80:
			out = append(out, '\\', 'x', hexits[c>>4], hexits[c&0xf])
		default:
			goleanShimUnsupported("golean fmt shim: %q over a non-ASCII byte is outside the modeled subset (fail closed; the modeled %q covers ASCII)")
			panic("unreachable: the machine stopped in goleanShimUnsupported above")
		}
	}
	out = append(out, '"')
	return string(out)
}

// goleanShimFmtStringVerb applies the VERB to a method result that has
// already been produced. gc's fmt hands the String()/Error() result to
// the same code that formats a plain string, so %x hexes it (two
// lowercase hexits per byte, zero-padded: probed "\x01\x0f\xff" ->
// 010fff) and %q quotes it; %s and %v pass it through. The PANIC render
// never reaches here (probed: %!x(PANIC=String method: ...) verbatim,
// not hex) — which is exactly why the recover lives in its own frame
// below and this call sits OUTSIDE it. If it sat inside, %q's
// fail-closed non-ASCII panic would be caught and re-rendered as a
// String-method panic: a silent wrong answer replacing a refusal.
// [Since audit R4-C-3 the refusal is a goleanShimUnsupported THROW
// that no recover can catch, so the frame placement is no longer
// load-bearing for refusals — it remains load-bearing for GENUINE
// user-method panics, whose render must not verb-process.]
func goleanShimFmtStringVerb(verb string, s string) string {
	if verb == "x" {
		return goleanShimFmtHexString(s)
	}
	if verb == "q" {
		return goleanShimFmtQuoteString(s)
	}
	return s
}

func goleanShimFmtHexString(s string) string {
	hexits := "0123456789abcdef"
	out := []byte{}
	for i := 0; i < len(s); i++ {
		c := s[i]
		out = append(out, hexits[c>>4], hexits[c&0xf])
	}
	return string(out)
}

func goleanShimFmtRender(verb string, method string, isNilPtr bool, call func() string) string {
	s, panicked := goleanShimFmtRenderCall(verb, method, isNilPtr, call)
	if panicked {
		return s
	}
	return goleanShimFmtStringVerb(verb, s)
}

func goleanShimFmtRenderCall(verb string, method string, isNilPtr bool, call func() string) (out string, panicked bool) {
	defer func() {
		if r := recover(); r != nil {
			panicked = true
			if isNilPtr {
				out = "<nil>"
				return
			}
			out = "%!" + verb + "(PANIC=" + method + " method: " + goleanShimFmtPanicValue(r) + ")"
		}
	}()
	return call(), false
}

func goleanShimFmtError(verb string, v error) string {
	if v == nil {
		if verb == "v" {
			return "<nil>"
		}
		return "%!" + verb + "(<nil>)"
	}
	s, panicked := goleanShimFmtErrorCall(verb, v)
	if panicked {
		return s
	}
	return goleanShimFmtStringVerb(verb, s)
}

func goleanShimFmtErrorCall(verb string, v error) (out string, panicked bool) {
	defer func() {
		if r := recover(); r != nil {
			panicked = true
			out = "%!" + verb + "(PANIC=Error method: " + goleanShimFmtPanicValue(r) + ")"
		}
	}()
	return v.Error(), false
}

func goleanShimFmtPanicValue(r any) string {
	if s, ok := r.(string); ok {
		return s
	}
	if e, ok := r.(error); ok {
		return e.Error()
	}
	goleanShimUnsupported("golean fmt shim: a String/Error method panicked with a value kind outside the modeled subset (fail closed)")
	panic("unreachable: the machine stopped in goleanShimUnsupported above")
}

// The %<width>d family (W4.3 item 1): space-pad LEFT to the width, the
// sign inside the padding, no truncation when the digits are wider —
// gc-probed (artifacts/w43/probe-fmt E1-E4: "    7", "123456", "  -42").
func goleanShimFmtPadLeft(s string, w int) string {
	for len(s) < w {
		s = " " + s
	}
	return s
}

func goleanShimFmtIntPad(v int64, w int) string {
	return goleanShimFmtPadLeft(goleanShimFmtInt(v), w)
}

func goleanShimFmtUintPad(v uint64, w int) string {
	return goleanShimFmtPadLeft(goleanShimFmtUint(v), w)
}
`,

	// The DYNAMIC fmt family (W4.3 item 1 landing C — cause 9): Sprintf/
	// Sprint/Sprintln with a SPREAD []any argument (the DefaultLogger
	// bodies; the replay env's recording logger). The format string is
	// parsed at RUNTIME over the same verb set as the static desugar
	// (%d %x %s %v %+v %q %t %%; no width/flags — no logger site uses
	// them), and each verb dispatches on the argument's DYNAMIC kind:
	// error and Stringer first for the stringable verbs (through the
	// injected goleanShimStringer interface — every String method
	// becomes a reachability candidate through this edge, priced in now
	// that the renderers lower), then a type switch over the basic
	// kinds + []byte + []uint64 + []int + []string (the last two:
	// audit R4-M-2). ANYTHING ELSE STOPS FAIL-CLOSED through
	// goleanShimUnsupported, naming the verb (a named non-Stringer
	// int, a float, a named STRUCT at runtime — the recorded R4-M-2
	// bound, row fmt/sprintf-dyn/struct-bound): a visible UNRECOVERABLE
	// machine stop (R4-C-3), never a silent wrong answer.
	// gc probes: artifacts/w43/probe-fmt K1-K3 (Sprint's space rule:
	// a space iff NEITHER neighbor is a string), artifacts/w43/probe-b
	// L1-L2 (Sprintln: spaces always, trailing newline), D3
	// (Sprint(nil) -> "<nil>").
	fmtDynShimKey: `
// goleanShimFmtDyn* are the native frontend's dynamic-fmt helpers
// (W4.3 item 1 landing C). Injected declarations — not user code.
type goleanShimStringer interface{ String() string }

// RECORDED BOUND (audit R1-F2): fmt.Formatter is INVISIBLE here. gc
// consults Format ahead of error/Stringer for every verb, but this
// shim runs inside the model with no reflection — it cannot ask "does
// the dynamic type implement fmt.Formatter" (fmt.State is unmodeled,
// so no goleanShim interface can name Format's signature). A dynamic
// value whose type implements BOTH Formatter and error/Stringer would
// render through Error/String here where gc calls Format — a wrong
// answer this shim cannot detect. Static sites refuse Formatter
// implementors (refuseFormatter, fmtdesugar.go), so the exposure is
// exactly: a Formatter implementor reaching a dyn site THROUGH an
// any/variadic boxing the static desugar cannot see. CLOSED at emit
// time since 2026-08-31 (t1-fidelity-fixes; assessment A3-S3):
// checkFormatterDynHole (fmtdesugar.go) refuses the whole export
// whenever this bundle is injected AND any declared type implements
// fmt.Formatter — the shim itself still cannot see Formatter, but no
// implementor can reach it anymore (pinned by
// fmt/formatter-dyn-hole/dyn-boxed).
func goleanShimFmtDynVerb(verb string, a any) string {
	if verb == "%" {
		goleanShimUnsupported("golean fmt shim: unreachable %% arm")
		panic("unreachable: the machine stopped in goleanShimUnsupported above")
	}
	if verb == "s" || verb == "v" || verb == "x" || verb == "q" {
		if e, ok := a.(error); ok {
			return goleanShimFmtError(verb, e)
		}
		if s, ok := a.(goleanShimStringer); ok {
			return goleanShimFmtRender(verb, "String", false,
				func() string { return s.String() })
		}
	}
	switch v := a.(type) {
	case nil:
		if verb == "v" {
			return "<nil>"
		}
	case bool:
		if verb == "v" || verb == "t" {
			return goleanShimFmtBool(v)
		}
	case string:
		if verb == "s" || verb == "v" {
			return v
		}
		if verb == "q" {
			return goleanShimFmtQuoteString(v)
		}
		if verb == "x" {
			return goleanShimFmtHexString(v)
		}
	case int:
		return goleanShimFmtDynInt(verb, int64(v))
	case int8:
		return goleanShimFmtDynInt(verb, int64(v))
	case int16:
		return goleanShimFmtDynInt(verb, int64(v))
	case int32:
		return goleanShimFmtDynInt(verb, int64(v))
	case int64:
		return goleanShimFmtDynInt(verb, v)
	case uint:
		return goleanShimFmtDynUint(verb, uint64(v))
	case uint8:
		return goleanShimFmtDynUint(verb, uint64(v))
	case uint16:
		return goleanShimFmtDynUint(verb, uint64(v))
	case uint32:
		return goleanShimFmtDynUint(verb, uint64(v))
	case uint64:
		return goleanShimFmtDynUint(verb, v)
	case []byte:
		if verb == "s" {
			return string(v)
		}
		if verb == "q" {
			return goleanShimFmtQuoteBytes(v)
		}
		if verb == "v" || verb == "d" {
			out := "["
			for i := 0; i < len(v); i++ {
				if i > 0 {
					out += " "
				}
				out += goleanShimFmtUint(uint64(v[i]))
			}
			return out + "]"
		}
	case []uint64:
		if verb == "v" || verb == "d" {
			out := "["
			for i := 0; i < len(v); i++ {
				if i > 0 {
					out += " "
				}
				out += goleanShimFmtUint(v[i])
			}
			return out + "]"
		}
	// []int / []string (audit R4-M-2): the dyn arms of two kinds the
	// STATIC composite matrix already renders — the leaves are the
	// same goleanShimFmt* helpers as the static cells, so the two
	// matrices agree by construction. Named STRUCTS stay a RECORDED
	// bound: a runtime type switch in pre-typecheck injected source
	// cannot name user types, and the static render path is emit-time
	// type recursion a runtime dispatch cannot reach (rows
	// fmt/sprintf-dyn/{slice-int,slice-string} green,
	// fmt/sprintf-dyn/struct-bound red-by-design).
	case []int:
		if verb == "v" || verb == "d" {
			out := "["
			for i := 0; i < len(v); i++ {
				if i > 0 {
					out += " "
				}
				out += goleanShimFmtInt(int64(v[i]))
			}
			return out + "]"
		}
	case []string:
		if verb == "v" || verb == "s" {
			out := "["
			for i := 0; i < len(v); i++ {
				if i > 0 {
					out += " "
				}
				out += v[i]
			}
			return out + "]"
		}
	}
	goleanShimUnsupported("golean fmt shim: dynamic verb %" + verb + " over an unmodeled dynamic kind (fail closed)")
	panic("unreachable: the machine stopped in goleanShimUnsupported above")
}

func goleanShimFmtDynInt(verb string, v int64) string {
	if verb == "d" || verb == "v" {
		return goleanShimFmtInt(v)
	}
	if verb == "x" && v >= 0 {
		return goleanShimFmtHex(uint64(v))
	}
	goleanShimUnsupported("golean fmt shim: dynamic verb %" + verb + " over a signed-integer kind (fail closed)")
	panic("unreachable: the machine stopped in goleanShimUnsupported above")
}

func goleanShimFmtDynUint(verb string, v uint64) string {
	if verb == "d" || verb == "v" {
		return goleanShimFmtUint(v)
	}
	if verb == "x" {
		return goleanShimFmtHex(v)
	}
	goleanShimUnsupported("golean fmt shim: dynamic verb %" + verb + " over an unsigned-integer kind (fail closed)")
	panic("unreachable: the machine stopped in goleanShimUnsupported above")
}

func goleanShimFmtSprintfDyn(format string, args []any) string {
	out := ""
	ai := 0
	i := 0
	for i < len(format) {
		c := format[i]
		if c != '%' {
			out += string(format[i : i+1])
			i++
			continue
		}
		if i+1 >= len(format) {
			goleanShimUnsupported("golean fmt shim: dynamic format string ends in % (fail closed)")
			panic("unreachable: the machine stopped in goleanShimUnsupported above")
		}
		i++
		verb := format[i : i+1]
		if verb == "%" {
			out += "%"
			i++
			continue
		}
		if verb == "+" {
			if i+1 < len(format) && format[i+1] == 'v' {
				verb = "v"
				i++
			} else {
				// The trailing-"%+" slice must be GUARDED (audit
				// R4-M-5): format[i+1:i+2] with i+1 == len was a Go
				// slice-bounds panic — the intended refusal came out
				// as a recoverable, mislabeled runtime error (row
				// fmt/sprintf-dyn/trailing-plus witnessed it live).
				trail := "<end of format>"
				if i+1 < len(format) {
					trail = format[i+1 : i+2]
				}
				goleanShimUnsupported("golean fmt shim: dynamic verb %+" + trail + " is outside the modeled subset (fail closed)")
				panic("unreachable: the machine stopped in goleanShimUnsupported above")
			}
		}
		if verb != "d" && verb != "x" && verb != "s" && verb != "v" && verb != "q" && verb != "t" {
			goleanShimUnsupported("golean fmt shim: dynamic verb %" + verb + " is outside the modeled subset (fail closed)")
			panic("unreachable: the machine stopped in goleanShimUnsupported above")
		}
		if ai >= len(args) {
			goleanShimUnsupported("golean fmt shim: dynamic format has more verbs than arguments (fmt would render a %! marker; fail closed)")
			panic("unreachable: the machine stopped in goleanShimUnsupported above")
		}
		out += goleanShimFmtDynVerb(verb, args[ai])
		ai++
		i++
	}
	if ai != len(args) {
		goleanShimUnsupported("golean fmt shim: dynamic format has fewer verbs than arguments (fmt would append %! extras; fail closed)")
		panic("unreachable: the machine stopped in goleanShimUnsupported above")
	}
	return out
}

func goleanShimFmtSprintDyn(args []any) string {
	out := ""
	prevString := false
	for i := 0; i < len(args); i++ {
		_, isStr := args[i].(string)
		if i > 0 && !prevString && !isStr {
			out += " "
		}
		out += goleanShimFmtDynVerb("v", args[i])
		prevString = isStr
	}
	return out
}

func goleanShimFmtSprintlnDyn(args []any) string {
	out := ""
	for i := 0; i < len(args); i++ {
		if i > 0 {
			out += " "
		}
		out += goleanShimFmtDynVerb("v", args[i])
	}
	return out + "\n"
}
`,


	shimUnsupportedName: `
// goleanShimUnsupported raises an UNRECOVERABLE machine stop (audit
// R4-C-3): the emitter force-quarantines this declaration
// (emitFuncDecl), so a CALL to it throws GoError.unsupported at the
// interpreter level — user recover() cannot catch it. Every
// golean-bound runtime refusal in the shim bodies routes through it;
// as plain panics they were catchable and recover() turned refusals
// into silent wrong answers. The Go body below exists for
// type-checking only — it is never lowered. Call sites follow it
// with panic("unreachable...") so Go's termination analysis is
// unchanged; that panic is dead (the throw fires first).
func goleanShimUnsupported(msg string) {
	panic(msg)
}
`,
}

// injectStdlibShims scans the parsed (pre-type-check) files for
// allowlisted stdlib selector calls and, when any is present, returns
// a synthetic file declaring the needed shims. The scan is SYNTACTIC
// (per-file import local names, then `local.Fn(...)` call shapes): a
// false positive merely injects a function the emitter never targets
// (dead on the wire, harmless); a false negative is impossible for the
// admitted shape because a qualified selector call must spell the
// import's local name in the same file — and the emitter's type-based
// hook fails closed if the shim it needs is ever absent.
func injectStdlibShims(fset *token.FileSet, files []*ast.File) (*ast.File, error) {
	needed := map[string]bool{}
	for _, f := range files {
		local := map[string]map[string]string{}
		localDesugar := map[string]map[string][]string{}
		localGeneric := map[string]map[string][]string{}
		for _, imp := range f.Imports {
			path := importPathOf(imp)
			fns, isShim := stdlibShimAllowlist[path]
			desugar, isDesugar := stdlibDesugarInject[path]
			generic, isGeneric := stdlibGenericDesugarInject[path]
			if !isShim && !isDesugar && !isGeneric {
				continue
			}
			// The default local name is the path's LAST SEGMENT (the
			// stdlib convention; exact for every listed package —
			// "encoding/binary" binds `binary`). A package whose name
			// diverged from its last segment would make this scan miss
			// — which fails CLOSED: no injection, and the emitter's
			// "shim not injected" refusal names the gap.
			name := path
			if i := lastSlash(path); i >= 0 {
				name = path[i+1:]
			}
			if imp.Name != nil {
				name = imp.Name.Name
			}
			// Dot and blank imports never produce the qualified
			// selector shape; they keep their existing behavior.
			if name == "." || name == "_" {
				continue
			}
			if isShim {
				local[name] = fns
			}
			if isDesugar {
				localDesugar[name] = desugar
			}
			if isGeneric {
				localGeneric[name] = generic
			}
		}
		if len(local) == 0 && len(localDesugar) == 0 && len(localGeneric) == 0 {
			continue
		}
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			x, ok := sel.X.(*ast.Ident)
			if !ok {
				return true
			}
			if fns, ok := local[x.Name]; ok {
				if shim, ok := fns[sel.Sel.Name]; ok {
					needed[shim] = true
				}
			}
			if desugar, ok := localDesugar[x.Name]; ok {
				for _, shim := range desugar[sel.Sel.Name] {
					needed[shim] = true
				}
			}
			if generic, ok := localGeneric[x.Name]; ok {
				for _, shim := range generic[sel.Sel.Name] {
					needed[shim] = true
				}
			}
			return true
		})
	}
	if len(needed) == 0 {
		return nil, nil
	}
	// Dependency closure (stdlibShimDeps, BUG-086): a shim whose SOURCE
	// calls another shim plants that shim too, transitively — BEFORE the
	// reserved-name scan, so every co-injected name is collision-checked
	// like the ones the program's calls named directly.
	if err := closeShimDeps(needed); err != nil {
		return nil, err
	}
	// Every shim bundle may route a runtime refusal through the
	// unsupported helper (R4-C-3), so it rides along whenever ANY shim
	// is injected — one dead declaration in the worst case, never a
	// missing one. Added BEFORE the reserved-name scan so it is
	// collision-checked like every other injected name.
	needed[shimUnsupportedName] = true
	// Reserved-name collision check: fail closed, loudly, BEFORE the
	// type-checker reports a bare redeclaration. Ranges over EVERY name
	// a needed shim injects (stdlibShimDeclNames), not just the key
	// declaration — the errors.New shim injects its concrete type too.
	reserved := map[string]bool{}
	for shim := range needed {
		for _, name := range stdlibShimDeclNames[shim] {
			reserved[name] = true
		}
	}
	for _, f := range files {
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				if d.Recv == nil && reserved[d.Name.Name] {
					return nil, fmt.Errorf("package declares %s, which is a reserved stdlib-shim name (E5); rename the declaration", d.Name.Name)
				}
			case *ast.GenDecl:
				for _, spec := range d.Specs {
					switch s := spec.(type) {
					case *ast.TypeSpec:
						if reserved[s.Name.Name] {
							return nil, fmt.Errorf("package declares %s, which is a reserved stdlib-shim name (E5); rename the declaration", s.Name.Name)
						}
					case *ast.ValueSpec:
						for _, id := range s.Names {
							if reserved[id.Name] {
								return nil, fmt.Errorf("package declares %s, which is a reserved stdlib-shim name (E5); rename the declaration", id.Name)
							}
						}
					}
				}
			}
		}
	}
	names := make([]string, 0, len(needed))
	for name := range needed {
		names = append(names, name)
	}
	sort.Strings(names)
	src := "package " + files[0].Name.Name + "\n"
	// The synthetic file has NO imports by construction: a shim names no
	// library declaration (a shim that did would couple injected text to
	// a library type — the `stdlibShimImports` coupling proposed and
	// DENIED at the D-002 exception, [USER] 2026-09-03, relayed).
	for _, name := range names {
		src += stdlibShimSources[name]
	}
	shimFile, err := parser.ParseFile(fset, "golean-stdlib-shims.go", src, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("internal: stdlib shim source failed to parse: %w", err)
	}
	return shimFile, nil
}

func lastSlash(s string) int {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == '/' {
			return i
		}
	}
	return -1
}

func importPathOf(imp *ast.ImportSpec) string {
	p := imp.Path.Value
	if len(p) >= 2 && p[0] == '"' && p[len(p)-1] == '"' {
		return p[1 : len(p)-1]
	}
	return p
}

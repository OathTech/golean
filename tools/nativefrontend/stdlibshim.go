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

// stringsFieldsShimName is the reserved declaration name of the
// strings.Fields shim ($-mangling is not available here: the injected
// file must parse as Go source, so the name is spellable and therefore
// collision-checked at injection instead).
const stringsFieldsShimName = "goleanShimStringsFields"

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

// The W4.1 item-4 smalls (docs/raft-w41-log.md item 4): strings.Join
// (H-17) and bytes.Equal (H-13) as ordinary E5 direct-call shims, and
// binary.LittleEndian.{Uint64,PutUint64} (H-14) as PACKAGE-VARIABLE
// METHOD desugars (the callee is a method on the exported var
// `binary.LittleEndian` of an unexported type, so the plain selector
// path cannot name it; fmtdesugar.go's emitBinaryVarMethodCall
// rewrites the two modeled methods to the shims below and every other
// member keeps failing closed).
const stringsJoinShimName = "goleanShimStringsJoin"
const bytesEqualShimName = "goleanShimBytesEqual"
const binaryLEUint64ShimName = "goleanShimLEUint64"
const binaryLEPutUint64ShimName = "goleanShimLEPutUint64"

// The W4.3 landing-B shims (docs/raft-w43-log.md item 1): strconv's
// Format/Parse trio (general bases 2..36; ParseUint's error TEXTS
// verbatim — the dynamic error TYPE is a recorded delta, upstream's
// *strconv.NumError vs the shim's string carrier, unobservable without
// asserting to the unexported upstream type), strings.Split (byte scan
// — upstream's own semantics for every non-empty separator; the empty
// separator's rune explode fails closed), strings.TrimSpace (the
// Fields byte-pattern table at both ends), strings.Repeat (loop concat
// + upstream's negative-count panic), slices.SortFunc (a GENERIC
// insertion-sort shim stenciled at the call's element type — emit.go's
// emitSortFuncCall; tie order is recorded latitude, upstream is "not
// guaranteed to be stable"), and cmp.Compare's kind shims (emit-time
// dispatch by static kind with explicit converts — floats excluded,
// NaN ordering is cmp.Compare-specific and unneeded).

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

const strconvFormatUintShimName = "goleanShimStrconvFormatUint"
const strconvFormatIntShimName = "goleanShimStrconvFormatInt"
const strconvParseUintShimName = "goleanShimStrconvParseUint"
const stringsSplitShimName = "goleanShimStringsSplit"
const stringsTrimSpaceShimName = "goleanShimStringsTrimSpace"
const stringsRepeatShimName = "goleanShimStringsRepeat"
const slicesSortFuncShimName = "goleanShimSlicesSortFunc"
const cmpCompareUintShimName = "goleanShimCmpCompareUint"
const cmpCompareIntShimName = "goleanShimCmpCompareInt"
const cmpCompareStringShimName = "goleanShimCmpCompareString"

// stdlibShimAllowlist: package import path -> selector name -> shim
// declaration name (the KEY declaration; a shim may inject more, see
// stdlibShimDeclNames).
var stdlibShimAllowlist = map[string]map[string]string{
	"strings": {"Fields": stringsFieldsShimName, "Join": stringsJoinShimName,
		"Split": stringsSplitShimName, "TrimSpace": stringsTrimSpaceShimName,
		"Repeat": stringsRepeatShimName},
	"errors": {"New": errorsNewShimName},
	"bytes":  {"Equal": bytesEqualShimName},
	"strconv": {"FormatUint": strconvFormatUintShimName,
		"FormatInt": strconvFormatIntShimName,
		"ParseUint": strconvParseUintShimName},
}

// stdlibGenericDesugarInject: packages whose GENERIC members desugar at
// emit time (emit.go: emitSortFuncCall / emitCmpCompareCall) — the
// injection scan must plant their shims on call presence, like
// stdlibDesugarInject, but they are not direct-call rewrites (the
// callee is generic: SortFunc stencils the injected generic shim at
// the element type; Compare dispatches to a kind shim with converts).
var stdlibGenericDesugarInject = map[string]map[string][]string{
	"slices": {"SortFunc": {slicesSortFuncShimName}},
	"cmp": {"Compare": {cmpCompareUintShimName, cmpCompareIntShimName,
		cmpCompareStringShimName}},
}

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

// stdlibVarMethodInject: package import path -> exported package
// VARIABLE -> method -> shims to inject when the two-level call shape
// `pkg.Var.Method(args)` occurs (fmtdesugar.go,
// emitBinaryVarMethodCall).
var stdlibVarMethodInject = map[string]map[string]map[string][]string{
	"encoding/binary": {
		"LittleEndian": {
			"Uint64":    {binaryLEUint64ShimName},
			"PutUint64": {binaryLEPutUint64ShimName},
		},
	},
}

// stdlibShimDeclNames: every RESERVED top-level name a shim injects,
// keyed by the shim's key declaration name. The collision check ranges
// over all of them — a user declaration matching ANY injected name
// refuses the export loudly (never a silent merge). Methods on shim
// types need no row: declaring one requires naming the receiver type,
// which is itself reserved here.
var stdlibShimDeclNames = map[string][]string{
	stringsFieldsShimName: {stringsFieldsShimName},
	errorsNewShimName:     {errorsNewShimName, errorsNewShimTypeName},
	fmtShimBundleKey: {fmtShimBundleKey, "goleanShimFmtInt", "goleanShimFmtHex",
		"goleanShimFmtBool", "goleanShimFmtQuoteBytes", "goleanShimFmtQuoteString",
		"goleanShimFmtStringVerb", "goleanShimFmtHexString", "goleanShimFmtRender",
		"goleanShimFmtRenderCall", "goleanShimFmtError", "goleanShimFmtErrorCall",
		"goleanShimFmtPanicValue", "goleanShimFmtIntPad", "goleanShimFmtUintPad",
		"goleanShimFmtPadLeft"},
	fmtDynShimKey: {fmtDynShimKey, "goleanShimStringer",
		"goleanShimFmtDynVerb", "goleanShimFmtDynInt", "goleanShimFmtDynUint",
		"goleanShimFmtSprintDyn", "goleanShimFmtSprintlnDyn"},
	stringsJoinShimName:       {stringsJoinShimName},
	bytesEqualShimName:        {bytesEqualShimName},
	binaryLEUint64ShimName:    {binaryLEUint64ShimName},
	binaryLEPutUint64ShimName: {binaryLEPutUint64ShimName},
	strconvFormatUintShimName: {strconvFormatUintShimName},
	strconvFormatIntShimName:  {strconvFormatIntShimName},
	strconvParseUintShimName: {strconvParseUintShimName,
		"goleanShimStrconvQuote", "goleanShimStrconvError"},
	stringsSplitShimName:     {stringsSplitShimName},
	stringsTrimSpaceShimName: {stringsTrimSpaceShimName},
	stringsRepeatShimName:    {stringsRepeatShimName},
	slicesSortFuncShimName:   {slicesSortFuncShimName},
	cmpCompareUintShimName:   {cmpCompareUintShimName},
	cmpCompareIntShimName:    {cmpCompareIntShimName},
	cmpCompareStringShimName: {cmpCompareStringShimName},
	shimUnsupportedName:      {shimUnsupportedName},
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
	// strings.Fields: "splits the string s around each instance of one
	// or more consecutive white space characters, as defined by
	// unicode.IsSpace, returning a slice of the substrings of s or an
	// empty slice if s contains only white space."
	//
	// The body is a BYTE scan over the FULL White_Space class —
	// unicode.IsSpace is a small closed set whose UTF-8 encodings are
	// finitely enumerable, so no rune decoding is needed:
	//   1 byte : 09 0A 0B 0C 0D 20
	//   2 bytes: C2 85 (U+0085 NEL), C2 A0 (U+00A0 NBSP)
	//   3 bytes: E1 9A 80 (U+1680); E2 80 80..8A (U+2000-200A);
	//            E2 80 A8, E2 80 A9 (U+2028/2029); E2 80 AF (U+202F);
	//            E2 81 9F (U+205F); E3 80 80 (U+3000)
	// No pattern starts with a UTF-8 continuation byte, so a pattern
	// can never fire from inside a preceding valid rune; on invalid
	// UTF-8 both sides treat undecodable bytes as field content
	// (RuneError is not white space). The separator-width computation
	// is INLINED (no helper function) so consumers' machine runs carry
	// no extra call frames.
	stringsFieldsShimName: `
// goleanShimStringsFields is the native frontend's strings.Fields shim
// (extension E5). Injected declaration — not user code. See
// tools/nativefrontend/stdlibshim.go for the contract and
// docs/gallery-campaign-log/g2.md for the fidelity argument.
func goleanShimStringsFields(s string) []string {
	out := []string{}
	i := 0
	start := 0
	inField := false
	for i < len(s) {
		w := 0
		c := s[i]
		if c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r' {
			w = 1
		} else if c == 0xC2 && i+1 < len(s) && (s[i+1] == 0x85 || s[i+1] == 0xA0) {
			w = 2
		} else if i+2 < len(s) {
			c1 := s[i+1]
			c2 := s[i+2]
			if (c == 0xE1 && c1 == 0x9A && c2 == 0x80) ||
				(c == 0xE2 && c1 == 0x80 && ((c2 >= 0x80 && c2 <= 0x8A) || c2 == 0xA8 || c2 == 0xA9 || c2 == 0xAF)) ||
				(c == 0xE2 && c1 == 0x81 && c2 == 0x9F) ||
				(c == 0xE3 && c1 == 0x80 && c2 == 0x80) {
				w = 3
			}
		}
		if w > 0 {
			if inField {
				out = append(out, s[start:i])
				inField = false
			}
			i += w
		} else {
			if !inField {
				start = i
				inField = true
			}
			i++
		}
	}
	if inField {
		out = append(out, s[start:])
	}
	return out
}
`,

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
	// kinds + []byte + []uint64. ANYTHING ELSE PANICS FAIL-CLOSED
	// naming the verb (a named non-Stringer int, a float, a struct at
	// runtime): a visible machine stop, never a silent wrong answer.
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
// any/variadic boxing the static desugar cannot see. Recorded, not
// closed; nothing in the subject tree implements fmt.Formatter.
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
				goleanShimUnsupported("golean fmt shim: dynamic verb %+" + format[i+1:i+2] + " is outside the modeled subset (fail closed)")
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

	// strings.Join: "concatenates the elements of its first argument to
	// create a single string. The separator string sep is placed between
	// elements in the resulting string." Plain concatenation is
	// byte-identical to upstream's Builder-based body (same elements,
	// same separators, in order); the conformance rows
	// (strings/join-conformance) pin it against the real one.
	stringsJoinShimName: `
// goleanShimStringsJoin is the native frontend's strings.Join shim
// (extension E5, raft W4.1 item 4). Injected declaration — not user
// code.
func goleanShimStringsJoin(elems []string, sep string) string {
	if len(elems) == 0 {
		return ""
	}
	out := elems[0]
	for i := 1; i < len(elems); i++ {
		out += sep
		out += elems[i]
	}
	return out
}
`,

	// bytes.Equal: "reports whether a and b are the same length and
	// contain the same bytes. A nil argument is equivalent to an empty
	// slice." Length-then-bytes gives exactly that (nil and empty both
	// have length 0); bytes/equal-conformance pins nil==empty TRUE.
	bytesEqualShimName: `
// goleanShimBytesEqual is the native frontend's bytes.Equal shim
// (extension E5, raft W4.1 item 4). Injected declaration — not user
// code.
func goleanShimBytesEqual(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
`,

	// binary.LittleEndian.Uint64/PutUint64: encoding/binary's own
	// bodies modulo names, including the leading bounds check whose
	// early out-of-range panic is part of the contract
	// (binary/little-endian/short-read pins it).
	binaryLEUint64ShimName: `
// goleanShimLEUint64 is the native frontend's
// binary.LittleEndian.Uint64 shim (raft W4.1 item 4). Injected
// declaration — not user code.
func goleanShimLEUint64(b []byte) uint64 {
	_ = b[7] // bounds check (upstream's early panic shape)
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}
`,

	binaryLEPutUint64ShimName: `
// goleanShimLEPutUint64 is the native frontend's
// binary.LittleEndian.PutUint64 shim (raft W4.1 item 4). Injected
// declaration — not user code.
func goleanShimLEPutUint64(b []byte, v uint64) {
	_ = b[7] // bounds check (upstream's early panic shape)
	b[0] = byte(v)
	b[1] = byte(v >> 8)
	b[2] = byte(v >> 16)
	b[3] = byte(v >> 24)
	b[4] = byte(v >> 32)
	b[5] = byte(v >> 40)
	b[6] = byte(v >> 48)
	b[7] = byte(v >> 56)
}
`,

	// strconv.FormatUint/FormatInt: digit loops over bases 2..36
	// (lowercase digits, upstream's alphabet), with upstream's exact
	// illegal-base panic (shared by both, from AppendInt/FormatInt —
	// gc-probed artifacts/w43/probe-b P6).
	strconvFormatUintShimName: `
// goleanShimStrconvFormatUint is the native frontend's
// strconv.FormatUint shim (W4.3 item 1 landing B). Injected
// declaration — not user code.
func goleanShimStrconvFormatUint(v uint64, base int) string {
	if base < 2 || base > 36 {
		panic("strconv: illegal AppendInt/FormatInt base")
	}
	digits := "0123456789abcdefghijklmnopqrstuvwxyz"
	if v == 0 {
		return "0"
	}
	out := []byte{}
	for v > 0 {
		out = append([]byte{digits[v%uint64(base)]}, out...)
		v /= uint64(base)
	}
	return string(out)
}
`,

	strconvFormatIntShimName: `
// goleanShimStrconvFormatInt is the native frontend's
// strconv.FormatInt shim (W4.3 item 1 landing B). Injected
// declaration — not user code.
func goleanShimStrconvFormatInt(v int64, base int) string {
	if base < 2 || base > 36 {
		panic("strconv: illegal AppendInt/FormatInt base")
	}
	if v < 0 {
		return "-" + goleanShimStrconvFormatUint(^uint64(v)+1, base)
	}
	return goleanShimStrconvFormatUint(uint64(v), base)
}
`,

	// strconv.ParseUint over explicit bases 2..36 and bitSize 0..64,
	// with upstream's two error TEXTS verbatim ("invalid syntax" /
	// "value out of range", the input quoted — gc-probed
	// artifacts/w43/probe-b P1-P5, P7; underscores are invalid outside
	// base 0, which matches the digit loop for free). RECORDED BOUNDS,
	// fail closed: base 0 (prefix detection) and bitSize outside 0..64
	// panic — the machine stops visibly where the real strconv would
	// parse; no subject site passes either. The error's dynamic TYPE is
	// the E5 delta (see the landing-B block comment).
	strconvParseUintShimName: `
// goleanShimStrconvParseUint and friends are the native frontend's
// strconv.ParseUint shim (W4.3 item 1 landing B). Injected
// declarations — not user code.
type goleanShimStrconvError struct{ s string }

func (e *goleanShimStrconvError) Error() string { return e.s }

func goleanShimStrconvQuote(s string) string {
	hexits := "0123456789abcdef"
	out := []byte{'"'}
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '"':
			out = append(out, '\\', '"')
		case c == '\\':
			out = append(out, '\\', '\\')
		case c >= 0x20 && c < 0x7f:
			out = append(out, c)
		case c == '\n':
			out = append(out, '\\', 'n')
		case c == '\t':
			out = append(out, '\\', 't')
		case c == '\r':
			out = append(out, '\\', 'r')
		case c < 0x80:
			out = append(out, '\\', 'x', hexits[c>>4], hexits[c&0xf])
		default:
			goleanShimUnsupported("golean strconv shim: quoting a non-ASCII input is outside the modeled subset (fail closed)")
			panic("unreachable: the machine stopped in goleanShimUnsupported above")
		}
	}
	out = append(out, '"')
	return string(out)
}

func goleanShimStrconvParseUint(s string, base int, bitSize int) (uint64, error) {
	if base < 2 || base > 36 {
		goleanShimUnsupported("golean strconv shim: ParseUint base outside 2..36 (base-0 prefix detection is outside the modeled subset; fail closed)")
		panic("unreachable: the machine stopped in goleanShimUnsupported above")
	}
	if bitSize == 0 {
		bitSize = 64
	}
	if bitSize < 0 || bitSize > 64 {
		goleanShimUnsupported("golean strconv shim: ParseUint bitSize outside 0..64 (fail closed)")
		panic("unreachable: the machine stopped in goleanShimUnsupported above")
	}
	syntaxErr := func() (uint64, error) {
		return 0, &goleanShimStrconvError{s: "strconv.ParseUint: parsing " + goleanShimStrconvQuote(s) + ": invalid syntax"}
	}
	rangeErr := func() (uint64, error) {
		return 0, &goleanShimStrconvError{s: "strconv.ParseUint: parsing " + goleanShimStrconvQuote(s) + ": value out of range"}
	}
	if len(s) == 0 {
		return syntaxErr()
	}
	var max uint64 = 1<<uint(bitSize) - 1
	if bitSize == 64 {
		max = 18446744073709551615
	}
	var v uint64
	for i := 0; i < len(s); i++ {
		c := s[i]
		var d uint64
		switch {
		case c >= '0' && c <= '9':
			d = uint64(c - '0')
		case c >= 'a' && c <= 'z':
			d = uint64(c-'a') + 10
		case c >= 'A' && c <= 'Z':
			d = uint64(c-'A') + 10
		default:
			return syntaxErr()
		}
		if d >= uint64(base) {
			return syntaxErr()
		}
		if v > (18446744073709551615-d)/uint64(base) {
			return rangeErr()
		}
		v = v*uint64(base) + d
		if v > max {
			return rangeErr()
		}
	}
	return v, nil
}
`,

	// strings.Split: byte scan, upstream's own semantics (genSplit is
	// strings.Index-based) for every NON-EMPTY separator; the empty
	// separator's per-rune explode fails closed (gc-probed
	// artifacts/w43/probe-b I1-I5, incl. the non-overlapping left scan).
	stringsSplitShimName: `
// goleanShimStringsSplit is the native frontend's strings.Split shim
// (W4.3 item 1 landing B). Injected declaration — not user code.
func goleanShimStringsSplit(s, sep string) []string {
	if len(sep) == 0 {
		goleanShimUnsupported("golean strings shim: Split with an empty separator (per-rune explode) is outside the modeled subset (fail closed)")
		panic("unreachable: the machine stopped in goleanShimUnsupported above")
	}
	out := []string{}
	start := 0
	i := 0
	for i+len(sep) <= len(s) {
		match := true
		for j := 0; j < len(sep); j++ {
			if s[i+j] != sep[j] {
				match = false
				break
			}
		}
		if match {
			out = append(out, s[start:i])
			i += len(sep)
			start = i
		} else {
			i++
		}
	}
	out = append(out, s[start:])
	return out
}
`,

	// strings.TrimSpace: both-ends trim of the full unicode White_Space
	// class via the SAME finite byte-pattern table as the Fields shim
	// (no pattern starts with a UTF-8 continuation byte, and the
	// multi-byte pattern leads C2/E1/E2/E3 cannot occur inside another
	// rune, so a pattern can never fire from inside a preceding rune —
	// the Fields shim's argument, unchanged). One forward pass records
	// the first non-space start and the byte after the last non-space.
	stringsTrimSpaceShimName: `
// goleanShimStringsTrimSpace is the native frontend's strings.TrimSpace
// shim (W4.3 item 1 landing B). Injected declaration — not user code.
func goleanShimStringsTrimSpace(s string) string {
	spaceW := func(i int) int {
		c := s[i]
		if c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r' {
			return 1
		}
		if c == 0xC2 && i+1 < len(s) && (s[i+1] == 0x85 || s[i+1] == 0xA0) {
			return 2
		}
		if i+2 < len(s) {
			c1 := s[i+1]
			c2 := s[i+2]
			if (c == 0xE1 && c1 == 0x9A && c2 == 0x80) ||
				(c == 0xE2 && c1 == 0x80 && ((c2 >= 0x80 && c2 <= 0x8A) || c2 == 0xA8 || c2 == 0xA9 || c2 == 0xAF)) ||
				(c == 0xE2 && c1 == 0x81 && c2 == 0x9F) ||
				(c == 0xE3 && c1 == 0x80 && c2 == 0x80) {
				return 3
			}
		}
		return 0
	}
	first := -1
	last := 0
	i := 0
	for i < len(s) {
		w := spaceW(i)
		if w > 0 {
			i += w
		} else {
			if first < 0 {
				first = i
			}
			i++
			last = i
		}
	}
	if first < 0 {
		return ""
	}
	return s[first:last]
}
`,

	// strings.Repeat: loop concatenation; upstream's negative-count
	// panic verbatim (gc-probed artifacts/w43/probe-b R1). Upstream's
	// output-length overflow panic is NOT modeled (the machine would
	// grow the string until fuel/memory bounds it — a visible stop,
	// never a wrong answer; recorded bound).
	stringsRepeatShimName: `
// goleanShimStringsRepeat is the native frontend's strings.Repeat shim
// (W4.3 item 1 landing B). Injected declaration — not user code.
func goleanShimStringsRepeat(s string, count int) string {
	if count < 0 {
		panic("strings: negative Repeat count")
	}
	out := ""
	for i := 0; i < count; i++ {
		out += s
	}
	return out
}
`,

	// slices.SortFunc: a GENERIC insertion sort, stenciled at the call
	// site's element type through the ordinary mono pipeline
	// (emit.go, emitSortFuncCall). Insertion sort is cmp-consistent —
	// the whole contract; upstream's "not guaranteed to be stable"
	// makes tie order LATITUDE (our member is stable; recorded, pinned
	// tie-insensitively by slices/sortfunc-cmp/sort-ties-projected).
	slicesSortFuncShimName: `
// goleanShimSlicesSortFunc is the native frontend's slices.SortFunc
// shim (W4.3 item 1 landing B). Injected declaration — not user code.
func goleanShimSlicesSortFunc[E any](x []E, cmp func(a, b E) int) {
	for i := 1; i < len(x); i++ {
		for j := i; j > 0 && cmp(x[j], x[j-1]) < 0; j-- {
			x[j], x[j-1] = x[j-1], x[j]
		}
	}
}
`,

	// cmp.Compare kind shims (emit-time dispatch with explicit
	// converts, emit.go's emitCmpCompareCall). For integer and string
	// kinds these are exactly cmp.Compare's semantics; floats (the NaN
	// arm) are excluded from the dispatch, so the shims never see them.
	cmpCompareUintShimName: `
// goleanShimCmpCompareUint is the native frontend's cmp.Compare shim
// at unsigned-integer kinds (W4.3 item 1 landing B). Injected
// declaration — not user code.
func goleanShimCmpCompareUint(a, b uint64) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
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

	cmpCompareIntShimName: `
// goleanShimCmpCompareInt is the native frontend's cmp.Compare shim at
// signed-integer kinds (W4.3 item 1 landing B). Injected declaration —
// not user code.
func goleanShimCmpCompareInt(a, b int64) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
}
`,

	cmpCompareStringShimName: `
// goleanShimCmpCompareString is the native frontend's cmp.Compare shim
// at string kinds (W4.3 item 1 landing B). Injected declaration — not
// user code.
func goleanShimCmpCompareString(a, b string) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
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
		localVarMethods := map[string]map[string]map[string][]string{}
		for _, imp := range f.Imports {
			path := importPathOf(imp)
			fns, isShim := stdlibShimAllowlist[path]
			desugar, isDesugar := stdlibDesugarInject[path]
			generic, isGeneric := stdlibGenericDesugarInject[path]
			varMethods, isVarMethod := stdlibVarMethodInject[path]
			if !isShim && !isDesugar && !isVarMethod && !isGeneric {
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
			if isVarMethod {
				localVarMethods[name] = varMethods
			}
		}
		if len(local) == 0 && len(localDesugar) == 0 &&
			len(localGeneric) == 0 && len(localVarMethods) == 0 {
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
		// The two-level package-VARIABLE method shape
		// (`binary.LittleEndian.Uint64(x)`): the callee's base is
		// itself a selector, so the ident scan above cannot see it.
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			sel2, ok := sel.X.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			x2, ok := sel2.X.(*ast.Ident)
			if !ok {
				return true
			}
			vars, ok := localVarMethods[x2.Name]
			if !ok {
				return true
			}
			methods, ok := vars[sel2.Sel.Name]
			if !ok {
				return true
			}
			for _, shim := range methods[sel.Sel.Name] {
				needed[shim] = true
			}
			return true
		})
	}
	if len(needed) == 0 {
		return nil, nil
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

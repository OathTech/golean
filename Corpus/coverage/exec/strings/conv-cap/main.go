// R3 / b6 — the capacity of []byte(s) and []rune(s). Spec §Conversions to and
// from a string type (both arms): "The capacity of the resulting slice is
// implementation-specific and may be larger than the slice length." gc
// go1.26.5 realizes FOUR regimes per conversion, decided by its typechecker,
// escape analysis and inlining — none visible as a property of the program
// (design note docs/2026-10-07_conv-cap-design.md §1, evidence
// docs/evidence/2026-10-07_conv-cap-design/envelope.tsv): a literal (or
// folded constant) operand → cap n; a non-literal result that is never
// written and does not escape → cap n (zero-copy: the slice ALIASES the
// string); a written, non-escaping result with n ≤ 32 → the 32-element
// conversion buffer (runes: for every n ≤ 32); an escaping result, or n > 32
// → roundupsize (bytes R(n); runes R(4n)/4). The machine draws
// ChoiceSite.convCap over EXACTLY gc's measured member set per (kind,
// literal?, len) — bytes non-literal {n} ∪ {R(n)} ∪ {32 | n ≤ 32}; runes
// non-literal {R(4n)/4} ∪ {32 | n ≤ 32}; literal {n} — and these rows witness
// every member (the standing rule: a widening admits only what the spec
// permits AND the pinned gc realizes, differentially witnessed). The runtime
// strings are built by concatenation, never strings.Repeat (source-through
// Builder growth would add append-spill consults to every row).
package main

var sinkB []byte
var sinkR []rune

//go:noinline
func mkA(n int) string {
	s := ""
	for i := 0; i < n; i++ {
		s += "a"
	}
	return s
}

//go:noinline
func mkE(n int) string {
	s := ""
	for i := 0; i < n; i++ {
		s += "é"
	}
	return s
}

// ---- literal controls: one member (cap = len), a bound-1 consult that pops nothing

func bytesLit() int { b := []byte("hello"); return cap(b) }

const k = "hello"

// A named constant folds to the literal operand (the frontend folds it like gc's typechecker).
func bytesConstLit() int { b := []byte(k); return cap(b) }

type B []byte

// A literal under a named slice type: still the literal operand (D3's control row).
func bytesNamedLit() int { b := B("hello"); return cap(b) }

func runesLit() int { r := []rune("héllo"); return cap(r) }

// ---- bytes, non-literal operand, result only read (gc: the zero-copy member, cap = len)

func bytesVarNomut0() int   { s := mkA(0); b := []byte(s); return cap(b) }
func bytesVarNomut5() int   { s := mkA(5); b := []byte(s); return cap(b) }
func bytesVarNomut33() int  { s := mkA(33); b := []byte(s); return cap(b) }
func bytesVarNomut100() int { s := mkA(100); b := []byte(s); return cap(b) }

// ---- bytes, non-literal operand, one element written (gc: the 32-byte buffer at n ≤ 32, R(n) above)

func bytesVarMut0() int {
	s := mkA(0)
	b := []byte(s)
	if len(b) > 0 {
		b[0] = 'x'
	}
	return cap(b)
}

func bytesVarMut5() int {
	s := mkA(5)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

func bytesVarMut33() int {
	s := mkA(33)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

func bytesVarMut100() int {
	s := mkA(100)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

// ---- bytes, non-literal operand, escaping result (gc: R(n))

func bytesVarEsc0() int   { s := mkA(0); b := []byte(s); sinkB = b; return cap(b) }
func bytesVarEsc5() int   { s := mkA(5); b := []byte(s); sinkB = b; return cap(b) }
func bytesVarEsc33() int  { s := mkA(33); b := []byte(s); sinkB = b; return cap(b) }
func bytesVarEsc100() int { s := mkA(100); b := []byte(s); sinkB = b; return cap(b) }

// ---- bytes, a concatenation operand (gc's walkAddString path), escaping

func bytesConcatEsc5() int { s := mkA(4) + "a"; b := []byte(s); sinkB = b; return cap(b) }

// ---- runes, non-literal operand, read only (gc: the 32-rune buffer at n ≤ 32, R(4n)/4 above)

func runesVarNomut5() int   { s := mkE(5); r := []rune(s); return cap(r) }
func runesVarNomut33() int  { s := mkE(33); r := []rune(s); return cap(r) }
func runesVarNomut100() int { s := mkE(100); r := []rune(s); return cap(r) }

// ---- runes, non-literal operand, escaping (gc: R(4n)/4)

func runesVarEsc5() int   { s := mkE(5); r := []rune(s); sinkR = r; return cap(r) }
func runesVarEsc33() int  { s := mkE(33); r := []rune(s); sinkR = r; return cap(r) }
func runesVarEsc100() int { s := mkE(100); r := []rune(s); sinkR = r; return cap(r) }

// ---- the inlined helper: ONE source line realizing two members in ONE run
// (at an inlined call the conversion's regime is the CALLER's: read-only → 5,
// written → 32; under -gcflags=-l the returned slice escapes → 8).

func conv(s string) []byte { return []byte(s) }

func bytesInlineHelper() (int, int) {
	s := mkA(5)
	b := conv(s)
	c := conv(s)
	c[0] = 'x'
	return cap(b), cap(c)
}

// ---- the aliasing witnesses: append on the converted slice, then a write,
// observed through the ORIGINAL — in place when the capacity has room (the
// 32-byte buffer; R(n) > n), a spill when cap = len.

func bytesAliasAppendMut5() (int, int) {
	s := mkA(5)
	b := []byte(s)
	c := append(b, 'x')
	c[0] = 'y'
	return cap(b), int(b[0])
}

func bytesAliasAppendEsc8() (int, int) {
	s := mkA(8)
	b := []byte(s)
	sinkB = b
	c := append(b, 'x')
	c[0] = 'y'
	return cap(b), int(b[0])
}

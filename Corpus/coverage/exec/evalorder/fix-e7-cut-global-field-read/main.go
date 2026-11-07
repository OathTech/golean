package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding D: the FIELD of a
// PACKAGE-LEVEL struct variable read beside a call that writes it, in a sweep the unseq grammar admits.
// The lowering spells `v.n` as `field-get(deref(globaladdr v))` — the E1 family's spelling of a global
// read under the E2 field head — and the decoder's fragment refused the receiver as a non-atom pointer,
// so the WHOLE wire was refused (status error) where gc runs the program. The fragment now admits the
// globaladdr under the field head (GoLean/NativeToIR.lean unseqCheckHead; the native unseq-wire witness
// e2gfld). Both subjects are membership rows: the read of v.n is spec-unsequenced against set(), the
// machine's set is {0, 500}; gc exhibits 500 on plainArg (call-first) and 0 on boxedLiteral (the read
// inside a struct literal boxed into `any` — gc's order pass copies the needsaddr literal at its
// position, finding B's class).

type V struct{ n int }
type P struct{ a, b int }

var v V

func set() int                 { v.n = 5; return 0 }
func sink(a, k int) int        { return a*100 + k }
func sinkAny(x any, k int) int { return x.(P).a*100 + k }

func plainArg() int     { return sink(v.n, set()) }
func boxedLiteral() int { return sinkAny(P{v.n, 0}, set()) }

func main() { println(plainArg(), boxedLiteral()) }

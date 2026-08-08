package main

// Tuple forwarding `g(f())` into interface-typed parameter slots must box
// each forwarded component exactly like an ordinary argument would
// (spec: assignability of each value of f()'s tuple to g's parameters).
// External Codex review 2026-08-08 (docs/2026-08-08_semantic-divergence-review.md
// §1, BUG-049): emitCallArgs' splat arm returned the raw splat temps without
// wrapInterfaceConversion, so the machine received unboxed values in `any`
// slots. Full six-form matrix — the review warns an (any,any)-only pin can
// miss per-position errors, so the mixed and fixed-plus-variadic forms pin
// the exact slot that needs boxing.

func pairIS() (int, string) { return 7, "x" }

func pairAA() (any, any) { return 7, "x" }

func sinkAnyAny(a, b any) int { return a.(int) + len(b.(string)) }

func sinkVariadicAny(xs ...any) int { return xs[0].(int) + len(xs[1].(string)) }

func sinkIntAny(a int, b any) int { return a + len(b.(string)) }

func sinkIntVariadicAny(a int, xs ...any) int { return a + len(xs[0].(string)) }

func sinkIntString(a int, b string) int { return a + len(b) }

// (int, string) -> (any, any): both slots box.
func tupleForwardFixedAny() int { return sinkAnyAny(pairIS()) }

// (int, string) -> ...any: both variadic elements box.
func tupleForwardVariadicAny() int { return sinkVariadicAny(pairIS()) }

// (int, string) -> (int, any): only the SECOND slot boxes (per-position).
func tupleForwardMixed() int { return sinkIntAny(pairIS()) }

// (int, string) -> (int, ...any): the variadic element boxes, the fixed
// slot does not.
func tupleForwardFixedPlusVariadic() int { return sinkIntVariadicAny(pairIS()) }

// (int, string) -> (int, string): control — no boxing anywhere.
func tupleForwardConcreteControl() int { return sinkIntString(pairIS()) }

// (any, any) -> (any, any): control — already-interface components need no
// conversion.
func tupleForwardInterfaceSourceControl() int { return sinkAnyAny(pairAA()) }

func main() {
	tupleForwardFixedAny()
	tupleForwardVariadicAny()
	tupleForwardMixed()
	tupleForwardFixedPlusVariadic()
	tupleForwardConcreteControl()
	tupleForwardInterfaceSourceControl()
}

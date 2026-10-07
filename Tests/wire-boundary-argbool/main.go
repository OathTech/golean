package main

// The entry-argument fixture (`--arg-bool`, 2026-10-07): `pick` takes an
// int, a bool, a DECLARED bool and a declared uint8, so one call mixes
// `--arg-int` and `--arg-bool` in positional order and reaches both
// declared-underlying resolutions. The controls in
// scripts/check-wire-boundary run it through the real CLI: the mixed call
// answers pick(1, true, false, 2) = 103 (and the other bool order 1001+2),
// and every mistyped, malformed, out-of-range or wrong-arity call refuses
// naming its cause.

type Flag bool
type Small uint8

func pick(n int, b bool, f Flag, s Small) int {
	r := n
	if b {
		r += 100
	}
	if bool(f) {
		r += 1000
	}
	return r + int(s)
}

func main() {
	println(pick(1, true, false, 2))
}

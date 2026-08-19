package main

// Multi-package guardrail, PINNED RED (raft W1.1 delta-review fix
// round, 2026-08-18; BUG-061, ledger L-0xx `spec-ambiguity`). The
// representative of the frontend's KNOWN residual on gc's pruning
// rule.
//
// The frontend decides "does this package have residual initialization
// work?" syntactically: a `func init()` with a non-empty body, or a
// package-scope variable initializer that go/types did NOT fold to a
// constant. gc's real answer is "what survives
// cmd/compile/internal/staticinit", which folds strictly MORE than
// constant expressions — composite literals of static elements, copies
// from other statically initialized globals, addresses of globals,
// conversions of constants, and (with the inliner on) whole function
// calls.
//
// So the frontend UNDER-PRUNES: it can call a package a node that gc
// pruned, never the reverse. Here `zq`'s only initializer is
// `[3]int{1, 2, 3}` — no constant value, so the frontend keeps `zq` in
// the schedule; gc writes the array into the data section and drops
// `zq` entirely.
//
//	gc:        zq pruned  =>  la ready at step one, wins on sort  =>  12
//	frontend:  zq a node  =>  la waits for zq, lb goes first      =>  21
//
// Measured, not assumed: a 26-flavor probe over the ways a package can
// be initialized (docs/spec-divergence-ledger.md) puts the residual at
// 11 of 26, all in this one direction, and this case is the
// representative composite-literal member. The 120-seed randomized
// differential harness is at 0 mismatches — it never generates a
// package whose initializers are static, which is exactly why this
// case is pinned by hand.
//
// WHY THE RESIDUAL IS NOT CHASED TO ZERO. One flavor of it — a
// variable initialized by a call to a foldable function — is not a
// property of the language at all: `go run` reports 12 and
// `go run -gcflags=all='-N -l'` reports 21 for the SAME source, so gc
// alone produces both orders depending on the inliner. Package
// initialization order is therefore not fully determined by the spec
// plus the program at the pruning boundary, and a rule that matched
// optimized gc exactly would be pinning one member of a genuinely wide
// envelope. See the ledger entry for the split and BUG-061 for what
// closing this would take.

import (
	_ "la"
	_ "lb"
	"rec"
)

// staticinitSeq is 12 under `go run`: gc folds `zq`'s array into the
// data section, so `zq` is not a node and gates nothing. The frontend
// reports 21. RED by design — the residual is visible, not hidden.
func staticinitSeq() int {
	return rec.Seq
}

func main() {}

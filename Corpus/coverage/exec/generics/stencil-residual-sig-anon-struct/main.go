package main

import "reflect"

// FR-4 RESIDUAL pin #1 (fr4-rowm audit fix round A5, 2026-09-04): a
// quarantined method STENCIL whose SIGNATURE does not lower even in
// SIGNATURE-OPAQUE mode — an anonymous non-empty struct parameter (FR-13)
// — still refuses the WHOLE export at quarantinedMethodStub's `sigRefusal`
// arm (no signature-carrying stub exists, so recording the method set
// would be incomplete; the same arm H-3's non-generic methods have). RED
// BY DESIGN at frontend-export; the innocent sibling is red for someone
// else's declaration, which is exactly the residual this row keeps
// visible. Flips when FR-13 (structural TypeIds) lands — and must then
// be retargeted, never let go green silently.

type box[T any] struct{ v T }

// bad: unlowerable BODY (reflect.TypeOf) AND an unlowerable SIGNATURE
// (anonymous struct parameter) — the stub cannot be built.
func (b box[T]) bad(p struct{ x int }) string { return reflect.TypeOf(b.v).String() + reflect.TypeOf(p).String() }

func (b box[T]) get() T { return b.v }

func sibling() int { return box[int]{v: 21}.get() * 2 } // 42 — never calls bad

func main() { println(sibling()) }

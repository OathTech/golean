package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding 3 on BUG-400: the
// fmt.Sprint space rule's kind oracle must carry an arm for a string-kinded generic INSTANTIATION that
// exists only as a STENCIL — `G[T]` inside a generic body, instantiated by `f[int]()` — and for one that
// reaches a non-generic Sprint site as an `any`. go/types' Instances record `G[T]` at the parameter, the
// site-time oracle skipped it, and the shim answered "not a string kind": gc `gxgy|gx1`, the machine
// `gx gy|gx 1`. The arms are now completed from the monomorphizer's stencil set at the end of emission.

import "fmt"

type G[T any] string

func (g G[T]) String() string { return "g" + string(g) }

type E[T any] string

func (e E[T]) Error() string { return "e" + string(e) }

type S string

func (s S) String() string { return "s" + string(s) }

func f[T any]() string { return fmt.Sprint(G[T]("x"), G[T]("y")) + "|" + fmt.Sprint(G[T]("x"), 1) }

func inStencil() string { return f[int]() }

func h[T any](x G[T]) string { return fmt.Sprint(x, x) + "|" + fmt.Sprint(x, 1) }
func f2[T any]() string      { return h[T](G[T]("x")) }

func nestedStencil() string { return f2[int]() + "|" + f2[bool]() }

func mk[T any]() any { return E[T]("x") }

func anyFromStencil() string { v := mk[int](); return fmt.Sprint(v, v) + "|" + fmt.Sprint(v, 2) }

func directBesideNamed() string {
	return fmt.Sprint(G[int]("a"), S("b")) + "|" + fmt.Sprint(S("b"), 1, G[string]("c"))
}

func main() { println(inStencil(), nestedStencil(), anyFromStencil(), directBesideNamed()) }

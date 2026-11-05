package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 — the E7 hidden-dependency channels the detector
// (tools/nativefrontend/hiddendep.go) did NOT cover before BUG-340's fix: a
// method VALUE taken through an interface, and an interface method PROMOTED
// through struct embedding. The DYNAMIC-target twins live here: with
// `var y = mark(1)` nothing folds under gc's staticinit, gc realizes the
// InitOrder literally and the two sides agree — and the detector, which
// since 2026-11-05 (lane frontend/fix-init-admission-1105) fires only on a
// target gc may fold, lets them lower. The static-target twins, refused by
// name since that fix, are init/sweep-s19-hidden-dep-funcvalue-static
// (BUG-340's Cases rows; one package per verdict, since the E7 refusal is
// whole-export).

// D3: a method value through an interface, called by a later initializer.
var trD3 int

func mkD3(x int) int { trD3 = trD3*10 + x; return x }

type d3I interface{ get() int }

type d3T struct{}

func (d3T) get() int { return d3y*10 + mkD3(2) }

var d3mv = d3I(d3T{}).get
var d3x = d3mv() + mkD3(3)
var d3y = mkD3(1)

func methodValueDynamic() int { return trD3*100 + d3x }

// D7: an interface method promoted through struct embedding.
var trD7 int

func mkD7(x int) int { trD7 = trD7*10 + x; return x }

type d7I interface{ val() int }

type d7T struct{}

func (d7T) val() int { return d7y*10 + mkD7(2) }

type d7S struct{ d7I }

var d7x = d7S{d7T{}}.val() + mkD7(3)
var d7y = mkD7(1)

func embeddedIfaceDynamic() int { return trD7*100 + d7x }

func main() {
	println(methodValueDynamic(), embeddedIfaceDynamic())
}

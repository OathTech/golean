package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27; split out of init/sweep-s19-hidden-dep-funcvalue at BUG-340's
// fix (lane frontend/fix-init-admission-1105, 2026-11-05) — the STATIC-target
// twins of the two E7 channels: a method VALUE taken through an interface
// (`var d3smv = d3sI(d3sT{}).gets; var d3sx = d3smv() + 3`) and an interface
// method PROMOTED through struct embedding (`d7sS{d7sT{}}.vals()`), each
// reading `var y = 4`, a constant gc's staticinit folds into the data section
// (gc 454) while the machine would assign it at its InitOrder position (54:
// the finding). Since the fix the detector covers both channels and REFUSES
// the export by name (FAIL/frontend-export, c-pin/hidden-dep-init-order — the
// same verdict as init/hidden-dep-refused); the expected column keeps gc's
// truth. RED BY DESIGN on BUG-340's Cases line. The dynamic twins stay in the
// original package and lower.

// D3, static target: a method value through an interface.
type d3sI interface{ gets() int }

type d3sT struct{}

func (d3sT) gets() int { return d3sy*10 + 2 }

var d3smv = d3sI(d3sT{}).gets
var d3sx = d3smv() + 3
var d3sy = 4

func methodValueStatic() int { return d3sx*10 + d3sy }

// D7, static target: an interface method promoted through struct embedding.
type d7sI interface{ vals() int }

type d7sT struct{}

func (d7sT) vals() int { return d7sy*10 + 2 }

type d7sS struct{ d7sI }

var d7sx = d7sS{d7sT{}}.vals() + 3
var d7sy = 4

func embeddedIfaceStatic() int { return d7sx*10 + d7sy }

func main() {
	println(methodValueStatic(), embeddedIfaceStatic())
}

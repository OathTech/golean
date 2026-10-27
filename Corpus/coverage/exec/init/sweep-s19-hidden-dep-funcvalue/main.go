package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 — the E7 hidden-dependency channels the detector
// (tools/nativefrontend/hiddendep.go) does NOT cover: a method VALUE
// taken through an interface, and an interface method PROMOTED through
// struct embedding. Neither is a CallExpr whose Fun is an interface
// MethodVal selection, which is what the detector's REACH condition keys
// on, so both programs lower and realize go/types' InitOrder, where x has
// no dependency on y and is initialized FIRST.
//
// THE MECHANISM, probed 2026-10-27: gc's own order is the SAME InitOrder
// (noder writes types2's `InitOrder`, the same analysis); its divergence
// on hidden dependencies comes from cmd/compile/internal/staticinit,
// which folds every STATIC initializer (`var y = 4`) into the data
// section at link time, so a dynamic initializer that reads y through a
// hidden channel sees 4 whatever its position in InitOrder. With a
// DYNAMIC target (`var y = mark(1)`) nothing folds and gc realizes the
// InitOrder literally — the two `*-dynamic` rows agree, the two
// `*-static` rows are BUG-340's red pins (gc 454, the machine 54).

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

type d3sI interface{ gets() int }

type d3sT struct{}

func (d3sT) gets() int { return d3sy*10 + 2 }

var d3smv = d3sI(d3sT{}).gets
var d3sx = d3smv() + 3
var d3sy = 4

func methodValueStatic() int { return d3sx*10 + d3sy }

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

type d7sI interface{ vals() int }

type d7sT struct{}

func (d7sT) vals() int { return d7sy*10 + 2 }

type d7sS struct{ d7sI }

var d7sx = d7sS{d7sT{}}.vals() + 3
var d7sy = 4

func embeddedIfaceStatic() int { return d7sx*10 + d7sy }

func main() {
	println(methodValueDynamic(), methodValueStatic(), embeddedIfaceDynamic(), embeddedIfaceStatic())
}

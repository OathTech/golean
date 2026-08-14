// E7 probe: the spec's own hidden-dependency shape (§Package
// initialization). hiddenX's initializer calls a method through an
// interface conversion — the dependency on hiddenA/hiddenB is hidden
// from per-package dependency analysis, so the order of hiddenX
// relative to hiddenA/hiddenB is unspecified. go/types' InitOrder
// (the frontend's realization) puts hiddenX FIRST -> 4242; gc's own
// initorder is recorded putting hiddenX after a/b -> 4624242.
package main

type hiddenI interface{ ab() int }

type hiddenT struct{}

func (hiddenT) ab() int { return hiddenA*10 + hiddenB }

var hiddenX = hiddenI(hiddenT{}).ab() // hidden dependency on hiddenA, hiddenB
var hiddenA = hiddenB
var hiddenB = 42

func main() {
	println(hiddenX*10000 + hiddenA*100 + hiddenB)
}

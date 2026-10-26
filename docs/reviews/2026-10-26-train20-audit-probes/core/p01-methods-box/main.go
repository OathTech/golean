package main

// Methods differ between the two types: A has none, B has M (value) and
// Bump (value receiver that mutates its copy). The box of *pb must carry B's
// method set; the pointer box dispatches at *B; the copy's mutation stays local.
type A struct{ X int }
type B struct{ X int }

func (B) M() string      { return "B" }
func (b B) Bump() int    { b.X++; return b.X }

type M interface{ M() string }

func probe() string {
	a := A{1}
	pb := (*B)(&a)
	var i M = *pb
	var j M = pb
	var k any = *pb
	_, okM := k.(M)
	var l any = a
	_, okAM := l.(M)
	r := i.M() + j.M()
	if okM {
		r += "y"
	} else {
		r += "n"
	}
	if okAM {
		r += "y"
	} else {
		r += "n"
	}
	n := pb.Bump()
	return r + string(rune('0'+n)) + string(rune('0'+a.X))
}

func main() { println(probe()) }

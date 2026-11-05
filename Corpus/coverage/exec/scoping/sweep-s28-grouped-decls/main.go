// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Grouped declarations in a
// function body — var, const and type groups, one-spec and empty groups, one-line groups
// with semicolons, a comment between specs — beside BUG-300's covered cell (a later spec
// reading an earlier one, open); expected = gc go1.26.5.

package main

type (
	gA int
	gB struct{ n int }
)

func (a gA) twice() int { return int(a) * 2 }
func (b gB) get() int   { return b.n }

func one() int { return 1 }

func groupedVarForms() int {
	var (a = 1)
	var (
		b int
		c string
	)
	var (d, e = 2, 3)
	var ()
	var (f = one())
	var (g = 4)
	var (h = g + 1)
	var (a2 = 5; b2 = 6)
	var (
		i = 7 // a comment after a spec
		// a comment between specs
		j = 8
	)
	b = 9
	c = "xy"
	return a + b*10 + len(c)*100 + d*1000 + e*10000 + f*100000 + h*1000000 + (a2+b2)*10000000 + (i+j)*100000000 // 1615312291
}

type myT int

func groupedConstForms() int {
	const (
		A = iota
		B
		C
	)
	const (D = 1)
	const ()
	const (E, F = 1, 2)
	const (
		G = iota
		_
		H
	)
	const (
		I myT = iota
		J
	)
	const (K = 3; L = K * 2)
	var v myT = J
	return A + B*10 + C*100 + D*1000 + E*10000 + F*100000 + G*1000000 + H*10000000 + int(v)*100000000 + L*1000000000 // 6121211210
}

func groupedTypeForms() int {
	type (
		lA int
		lB string
	)
	type (lC = int; lD lC)
	type ()
	var a lA = 3
	var b lB = "ab"
	var c lC = 4
	var d lD = 5
	ga := gA(6)
	gb := gB{7}
	return int(a) + len(b)*10 + c*100 + int(d)*1000 + ga.twice()*10000 + gb.get()*100000 // 825423
}

func main() {
	println("groupedVarForms", groupedVarForms())
	println("groupedConstForms", groupedConstForms())
	println("groupedTypeForms", groupedTypeForms())
}

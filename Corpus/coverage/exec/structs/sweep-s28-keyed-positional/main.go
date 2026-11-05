// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Keyed versus positional literal
// spellings: keyed and positional elements MIXED across the elements of one slice / map /
// pointer-element literal, keyed slice and array indices out of order, positional after
// keyed, a named-constant index, a nested keyed index; expected = gc go1.26.5.

package main

type pt struct{ a, b int }

const idx = 3

func mixedKeyedPositionalElements() int {
	s := []pt{{1, 2}, {a: 3}, {b: 4}, {5, 6}}
	m := map[string]pt{"x": {1, 2}, "y": {b: 7}, "z": {a: 8}}
	ps := []*pt{{1, 0}, {a: 9}, {b: 10}}
	arr := [2]pt{{a: 1}, {2, 3}}
	n := 0
	for _, p := range s {
		n = n*10 + p.a + p.b
	}
	n = n*100 + m["x"].a + m["y"].b + m["z"].a
	n = n*100 + ps[0].a + ps[1].a + ps[2].b
	n = n*100 + arr[0].a + arr[1].b
	return n // 3341118200404 → gc decides
}

func keyedIndexForms() int {
	a := []int{0: 1, 2: 3}
	b := [...]int{5: 1}
	c := [3]int{2: 9}
	d := []int{2: 1, 0: 5}
	e := []string{1: "b", "c"}
	f := []int{idx: 7}
	g := [][]int{1: {2: 3}}
	h := []int{(2): 1}
	i := [...]int{1: 10, 20, 0: 30}
	n := len(a)*1 + a[2]*10 + len(b)*100 + c[2]*1000 + len(d)*10000 + d[0]*100000 + len(e)*1000000
	n += len(f)*10000000 + f[idx]*100000000 + len(g[1])*1000000000
	return n*100 + len(h) + len(i)*10 + i[2] - 20 // gc decides
}

func main() {
	println("mixedKeyedPositionalElements", mixedKeyedPositionalElements())
	println("keyedIndexForms", keyedIndexForms())
}

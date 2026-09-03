// noodler frontier probe — IncDec / op= through an array pointer and a pointer to an array of structs
package main

// IncDec and compound assignment on elements through an array pointer
// and on a struct field through a pointer-to-array of structs.
func incDecArrayPointerElem() int {
	a := [3]int{1, 2, 3}
	p := &a
	p[0]++
	p[1] *= 10
	type S struct{ n int }
	ss := &[2]S{}
	ss[1].n += 7
	return a[0]*100 + a[1] + ss[1].n
}

func main() {}

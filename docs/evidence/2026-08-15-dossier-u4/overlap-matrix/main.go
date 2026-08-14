// U-4 probe: overlapping copy/append. Spec: "the result is
// independent of whether the memory referenced by the arguments
// overlaps" — FORCED as-if-intermediate semantics.
package main

func show(tag string, s []int) {
	print(tag, ": ")
	for _, v := range s {
		print(v, " ")
	}
	println()
}

func main() {
	// forward overlap: shift right within one array
	a := []int{1, 2, 3, 4, 5}
	n := copy(a[1:], a[:4])
	print("copied ", n, " | ")
	show("fwd  a[1:] <- a[:4]", a) // as-if: 1 1 2 3 4

	// backward overlap: shift left
	b := []int{1, 2, 3, 4, 5}
	n = copy(b[:4], b[1:])
	print("copied ", n, " | ")
	show("bwd  b[:4] <- b[1:]", b) // as-if: 2 3 4 5 5

	// total overlap: identity
	c := []int{1, 2, 3}
	copy(c, c)
	show("self c <- c        ", c) // 1 2 3

	// in-place append with aliasing dst/src (no growth: cap 8)
	d := make([]int, 3, 8)
	d[0], d[1], d[2] = 1, 2, 3
	e := append(d[:1], d...) // dst d[1:4] overlaps src d[0:3]
	show("append d[:1], d... ", e) // as-if: 1 1 2 3

	// self-append with growth (spill): src survives the copy
	f := []int{7, 8, 9}
	g := append(f, f...)
	show("append f, f...     ", g) // 7 8 9 7 8 9
}

package main

// The seeded-heap fixture (seeded-heap slice B, 2026-10-12; design
// docs/2026-10-09_seeded-heap-design.md §0's P1/P2 shapes): entry functions
// over POINTER parameters, run by `golean native-json-run --seed <file>` with
// `--arg-ref`/`--arg-nil`. The controls in scripts/check-wire-boundary (the
// seeded section) run it through the real CLI: inc on a seeded int, addNaive
// aliased and distinct, sum3 over a two-cell CYCLE, a pointer result into the
// seed rendered seed-relative, a pointer into an array cell's element, a nil
// argument; and the refusals by name — a bad type spelling, an ambiguous type
// (the two local types T), a bad path, a blank field (B), an argument type
// mismatch, an escaping pointer (retLocal), the enumerator/tracer refusing
// the seed flags. main() is the Go twin's shape (the prologue slice C
// generates), so the program also runs under `go run`.

type Node struct {
	next *Node
	val  int
}

type Pair struct {
	a [3]int
	b bool
}

type B struct {
	_ int
	x int
}

func inc(p *int) int {
	*p = *p + 1
	return *p
}

func addNaive(a, b *int) (int, int) {
	*a = *a + *b
	*b = *a + *b
	return *a, *b
}

func sum3(n *Node) int {
	return n.val + n.next.val + n.next.next.val
}

func next(n *Node) *Node {
	return n.next
}

func isNil(p *Node) bool {
	return p == nil
}

func retLocal(p *int) *int {
	x := *p
	return &x
}

func useB(b *B) int {
	return b.x
}

func local1() int {
	type T int
	var t T = 1
	return int(t)
}

func local2() bool {
	type T bool
	var t T = true
	return bool(t)
}

func main() {
	var c0 int = 41
	println(inc(&c0))
	var d0, d1 int = 5, 7
	x, y := addNaive(&d0, &d1)
	println(x, y)
	var n0, n1 Node
	n0 = Node{next: &n1, val: 2}
	n1 = Node{next: &n0, val: 3}
	println(sum3(&n0), next(&n0) == &n1, isNil(nil))
	var pr Pair
	pr.a[1] = 9
	println(inc(&pr.a[1]), *retLocal(&c0), useB(&B{x: 4}), local1(), local2())
}

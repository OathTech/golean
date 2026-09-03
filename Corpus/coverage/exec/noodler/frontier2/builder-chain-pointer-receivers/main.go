// noodler frontier probe — builder-style chained pointer-receiver calls
package main

type B struct{ parts []int }

func (b *B) Add(x int) *B { b.parts = append(b.parts, x); return b }
func (b *B) Sum() int {
	s := 0
	for _, p := range b.parts {
		s += p
	}
	return s
}

// Chained pointer-receiver calls on an addressable value and on &B{}.
func builderChainPointerReceivers() (int, int) {
	var b B
	b.Add(1).Add(2).Add(3)
	return b.Sum(), (&B{}).Add(10).Add(20).Sum()
}

func main() {}

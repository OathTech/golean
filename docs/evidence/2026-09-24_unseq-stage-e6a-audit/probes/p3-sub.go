package sub

func Wit(x int) int { println("wit", x); return x }

// a graph in a NON-MAIN unit: s[i] unordered against the effectful Wit
func G(s []int, i int) int { return s[i] + Wit(5) }

// mutates the caller's backing array
func Mut(s []int) int { s[0] = 99; return 1 }

type T struct{ N int }

func (t *T) Bump() int { t.N++; return t.N }

func (t T) Val() int { return t.N }

// a func-typed package variable — a `call-value` shape the graph refuses by name
var F = func(x int) int { return x + 1 }

func Id[X any](x X) X { return x }

func Sum(xs ...int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

// same-name collision with main's G
func H(s []int) int { return Mut(s) + s[0] }

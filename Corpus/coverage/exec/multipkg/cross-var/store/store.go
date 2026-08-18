package store

// Counter is mutated from OUTSIDE the package; Bump observes the
// same cell from inside it.
var Counter int

func Bump() int {
	Counter++
	return Counter
}

// staticinit-other.go — the foreign package the BUG-061 shape table reads
// (staticinit-shapes.go: FCopy = other.V, FFV = other.F). No work of its
// own: V is a constant initializer, F a function.
package other

var V = 1

func F() int { return 1 }

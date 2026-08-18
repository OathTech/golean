package rec

// rec has no initialization work of its own, so it is pruned under
// both rules and gates nothing either way.

// Seq accumulates one decimal digit per initialization event; the mark
// identifies the package (la = 1, lb = 2).
var Seq int

// Push records an event.
func Push(mark int) int {
	Seq = Seq*10 + mark
	return Seq
}

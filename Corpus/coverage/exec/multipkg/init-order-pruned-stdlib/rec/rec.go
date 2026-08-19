package rec

// rec has no initialization work of its own, so it is not a node
// either — nothing in this program gates anything.

// Seq accumulates one decimal digit per initialization event.
var Seq int

// Push records an event.
func Push(mark int) int {
	Seq = Seq*10 + mark
	return Seq
}

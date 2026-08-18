package rec

// rec has no initialization work of its own (no variable initializers,
// no init function), so gc emits no inittask for it and it gates
// neither importer: both x and x-y are ready at step one.

// Seq accumulates one decimal digit per initialization event; the mark
// identifies the package (x = 1, x-y = 2), so the value IS the
// observed schedule.
var Seq int

// Push records an event.
func Push(mark int) int {
	Seq = Seq*10 + mark
	return Seq
}

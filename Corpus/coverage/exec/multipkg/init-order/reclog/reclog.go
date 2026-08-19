package reclog

// Seq accumulates one decimal digit per initialization event,
// program-wide: the value IS the observed schedule.
var Seq int

var count int

// Push appends a mark and returns how many pushes have happened.
func Push(mark int) int {
	Seq = Seq*10 + mark
	count++
	return count
}

package rec

// The recorder: one decimal digit per initialization event, program-wide;
// no initializer and no init of its own, so rec is pruned and gates nothing.
var Seq int

// Push records an event and returns the mark.
func Push(m int) int { Seq = Seq*10 + m; return m }


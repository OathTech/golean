package zf

// A call to a body that is not a single return: not inlinable into a
// static value — work.
var F = zff()

func zff() int { x := 1; x++; return x }

package zh

// CONTROL: int -> int64 of a DYNAMIC global: staticcopy finds no static
// value to copy — work.
func zf() int { x := 1; x++; return x }

var zv = zf()
var C = int64(zv)

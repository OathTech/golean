package zv

// An interface call: OCALLINTER (devirtualized through a receiver
// assertion the static-init fold refuses) — work.
type zI interface{ m() int }
type zT struct{}

func (zT) m() int { return 1 }

var V = zI(zT{}).m()

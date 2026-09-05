// Package emb: a DISTINCT-named package (not `inner`) declaring an
// unexported `get` — the shape on which main answered WRONG before the
// BUG-098 guard (nothing fused, nothing tripped: the bare name matched).
package emb

type E struct{ V int }

func (E) get() int { return 1 }

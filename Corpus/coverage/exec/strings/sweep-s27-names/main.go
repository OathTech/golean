package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Non-ASCII IDENTIFIERS on the wire (encoding/json → StrictJson → the
// readout's typeName / field names / dynamic) against the Go side's reflect
// names: a struct type and its fields, a defined string type in an interface,
// a method dispatched through an interface, a local and a package-level var.
// The subject functions themselves are ASCII (the corpus manifest admits ASCII
// subject identifiers only); the non-ASCII SUBJECT name was probed by hand
// (the lane's report). A defined string type as a PANIC payload is the
// unpinned `printanycustomtype` form (BUG-004 item 2's scope) — not rowed.

type Größe struct {
	Füße   int
	Straße string
}

type Ärger string

type Messer interface {
	Größe() int
}

func (a Ärger) Größe() int { return len(a) }

var ß = "ẞ\xff"

func groesse() (Größe, int) {
	ü := "ü"
	return Größe{Füße: 2, Straße: ü + "\x00"}, len(ü)
}

func aergerInInterface() (any, int, string) {
	var m Messer = Ärger("é\xbf")
	var x any = Ärger("\xff")
	return x, m.Größe(), ß
}

func main() {
	groesse()
}

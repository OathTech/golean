package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-133's shape at the
// SEEDED READOUT route — a pointer into a seed cell taken through the
// converted spelling (`&(*aliasB)(p).X`) renders as the same seed-relative
// path as the direct spelling (`seedRelative?` keeps field NAMES, never the
// static typeId; the Go observer renders the address relative to the cell),
// and a pointer to the whole cell converted and back is the cell itself.

type aliasA struct {
	X int `json:"a"`
	Y int `json:"a"`
}
type aliasB struct {
	X int `json:"b"`
	Y int `json:"b"`
}

func viaAlias(p *aliasA) *int {
	return &(*aliasB)(p).Y
}

func direct(p *aliasA) *int {
	return &p.Y
}

func wholeBack(p *aliasA) *aliasA {
	return (*aliasA)((*aliasB)(p))
}

func main() {
	c := &aliasA{X: 1, Y: 2}
	println(viaAlias(c) == direct(c), wholeBack(c) == c)
}

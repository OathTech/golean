package main

// spec#Short_variable_declarations block
// Short_variable_declarations-3-b4785831: `:=` is shorthand for a
// regular var declaration with initializer expressions and no types —
// multiple variables at once, function literals, make results, and
// multi-value calls with the blank identifier discarding positions.
// Expected from the spec text: i == 0, j == 10, f() == 7, ch is a
// usable (non-nil, empty) channel, and only the wanted positions of
// the multi-value calls are kept.
// Adaptation: os.Pipe()/coord(p) are stand-ins here (svdPipe returns
// a connected pair of values and a nil error; svdCoord returns three
// coordinates) — the block's point is the declaration form, not os.

type svdPoint struct{ cx, cy, cz int }

func svdPipe() (int, int, error) { return 3, 4, nil }

func svdCoord(p svdPoint) (int, int, int) { return p.cx, p.cy, p.cz }

func shortVarDeclForms() (int, int, int, int, int) {
	p := svdPoint{cx: 8, cy: 20, cz: 31}
	i, j := 0, 10
	f := func() int { return 7 }
	ch := make(chan int)
	r, w, _ := svdPipe()  // returns a connected pair and an error, if any
	_, y, _ := svdCoord(p) // three values; only interested in y
	return i + j, f(), len(ch), r + w, y
}

func main() {
	shortVarDeclForms()
}

package main

// The choice-report fixture (F1 of the 2026-10-13 fail-closed pass): entry
// functions run by `golean native-json-run` in scripts/check-wire-boundary's
// choice-report section. spill consults the append-spill site once (bound 32:
// the envelope [1, 32] of a first append to a nil []byte — gc answers 32, the
// canonical member is 4); plain consults nothing; goro spawns a goroutine (the
// scheduler's sites); spillSeed is spill behind a seeded pointer parameter;
// spillPanic consults the spill site and then panics (a Stop ending: the
// driver returns no leftover tape, so the default report cannot count).

func spill() int {
	var b []byte
	b = append(b, 1)
	return cap(b)
}

func plain() int {
	return 42
}

func goro() int {
	ch := make(chan int)
	go func() { ch <- 41 }()
	return <-ch + 1
}

func spillSeed(p *int) int {
	var b []byte
	b = append(b, byte(*p))
	return cap(b) + *p
}

func spillPanic() int {
	var b []byte
	b = append(b, 1)
	var m map[int]int
	m[1] = cap(b)
	return 0
}

func main() {
	println(spill(), plain(), goro())
	x := 1
	println(spillSeed(&x))
}

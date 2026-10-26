package main

// DC01 neighbourhood, the detector side: two goroutines write ONE cell
// through POINTERS taken under two spellings (`p := &a.X`, `q := &b.X`
// after the tag-compatible conversion). gc `-race` reports the race; the
// machine keys its shadow by CANONICAL location (BUG-111's fix), so it
// refuses on every enumerated path — a `ok` here would be the fail-open
// twin of the DC01 wrong answer. Pinned beside BUG-111's selector-spelled
// rows (`race/negative/struct-tag-alias-*`), which write via `a.f`/`q.f`
// rather than through stored pointers.

type raceA struct {
	X int `json:"a"`
}
type raceB struct {
	X int `json:"b"`
}

func racePointerAlias() int {
	a := raceA{}
	p := &a.X
	q := &(*raceB)(&a).X
	done := make(chan int)
	go func() {
		*q = 1
		done <- 0
	}()
	*p = 2
	<-done
	return *p
}

func main() { println(racePointerAlias()) }

package main

// RED PIN (arc-final audit F9): UNNAMED channel types are outside the
// generic type-argument mangling surface — renderTypeArg (mono.go) has
// no *types.Chan arm, so ANY instantiation whose type argument
// structurally contains `chan int` is refused ("type argument outside
// the mangling surface"), even though (a) this generic performs NO
// channel operation and (b) channels have been a first-class wire type
// since the channels arc (the refusal's original "cannot reach a
// supported wire type" rationale is stale — corrected at the mono.go
// site). The NAMED spelling (type C chan int; the
// generics/type-parameter-channel-ops case) reaches the Named arm and
// works — this pin records the unnamed half red until a *types.Chan
// mangling arm lands.

func firstOf[T any](xs []T) T {
	return xs[0]
}

func chanTypeArgFirst() int {
	a := make(chan int, 1)
	a <- 5
	chans := []chan int{a}
	first := firstOf(chans)
	return <-first
}

func main() {
	chanTypeArgFirst()
}

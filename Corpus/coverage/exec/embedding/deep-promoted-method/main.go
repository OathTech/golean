package main

type deepMethodBase struct {
	n int
}

func (b deepMethodBase) value() int {
	return b.n + 1
}

type deepMethodMid struct {
	deepMethodBase
}

type deepMethodOuter struct {
	deepMethodMid
}

func deepPromotedMethod() int {
	x := deepMethodOuter{deepMethodMid: deepMethodMid{deepMethodBase: deepMethodBase{n: 6}}}
	return x.value()
}

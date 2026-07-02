package main

type deepLeaf struct {
	x int
}

type deepMid struct {
	deepLeaf
}

type deepOuter struct {
	deepMid
}

func deepPromotedField() int {
	o := deepOuter{deepMid: deepMid{deepLeaf: deepLeaf{x: 5}}}
	o.x = 9
	return o.deepMid.deepLeaf.x
}

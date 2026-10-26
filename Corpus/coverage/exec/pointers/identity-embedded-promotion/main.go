package main

// DC01 neighbourhood: PROMOTION is another route by which two spellings
// name one cell — `&a.X` (promoted through the embedded `emb`) and
// `&a.emb.X` (explicit). The frontend lowers the promoted selector to the
// explicit path (`fieldPathAddr`), so these agreed before the fix; the
// rows pin that route, and the alias+promotion combination (`&b.X` through
// a tag-compatible conversion of an embedding struct) that needed the fix.

type emb struct{ X int }
type hostA struct {
	emb
	Y int
}
type hostB struct {
	emb
	Y int
}

func promotedVsExplicit() bool {
	a := hostA{emb: emb{X: 1}, Y: 2}
	return &a.X == &a.emb.X
}

func promotedThroughAlias() bool {
	a := hostA{emb: emb{X: 1}, Y: 2}
	b := (*hostB)(&a)
	return &a.X == &b.X
}

func embeddedStructThroughAlias() bool {
	a := hostA{emb: emb{X: 1}, Y: 2}
	b := (*hostB)(&a)
	return &a.emb == &b.emb
}

func promotedVsSibling() bool {
	a := hostA{emb: emb{X: 1}, Y: 2}
	return any(&a.X) == any(&a.Y)
}

func main() {
	println(promotedVsExplicit(), promotedThroughAlias(), embeddedStructThroughAlias(), promotedVsSibling())
}

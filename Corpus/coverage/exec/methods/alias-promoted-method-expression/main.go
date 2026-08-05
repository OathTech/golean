package main

type ampBase struct {
	n int
}

func (b ampBase) Get() int {
	return b.n * 2
}

type ampWrap struct {
	ampBase
}

type ampWrapAlias = ampWrap

type ampBaseAlias = ampBase

func aliasPromotedMethodExpression() int {
	f := ampWrapAlias.Get
	return f(ampWrap{ampBase{n: 7}})
}

func aliasDirectMethodExpression() int {
	f := ampBaseAlias.Get
	return f(ampBase{n: 5})
}

func main() {
	aliasPromotedMethodExpression()
	aliasDirectMethodExpression()
}

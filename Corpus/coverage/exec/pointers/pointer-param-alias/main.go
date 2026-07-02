package main

func pointerParamBump(p *int) {
	*p = *p + 1
}

func pointerParamAlias() int {
	x := 6
	pointerParamBump(&x)
	pointerParamBump(&x)
	return x
}

func main() {
	pointerParamAlias()
}

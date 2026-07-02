package main

type deferInterfaceSaver interface {
	save(*int)
}

type deferInterfaceValue struct {
	n int
}

func (v deferInterfaceValue) save(dst *int) {
	*dst = v.n
}

func deferInterfaceValueEval() (result int) {
	var x deferInterfaceSaver = deferInterfaceValue{n: 2}
	defer x.save(&result)
	x = deferInterfaceValue{n: 8}
	return 0
}

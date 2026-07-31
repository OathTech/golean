package main

// Go has a DISTINCT panic shape when the assert TARGET is an interface:
// `interface conversion: <dyn> is not <Iface>: missing method <M>`, naming the
// first missing method in name order — and `interface conversion: interface is
// nil, not <Iface>` for a nil operand (pre-merge audit 2026-07-31, finding 7;
// the machine rendered the concrete-target shape for all four).

type twoMethod interface {
	M() int
	N() int
}

type onlyM struct{ n int }

func (o onlyM) M() int { return o.n }

func assertInterfaceMissingAll() int {
	var e any = 3
	return e.(twoMethod).M()
}

func assertInterfaceMissingOne() int {
	var e any = onlyM{n: 4}
	return e.(twoMethod).N()
}

func assertInterfaceNil() int {
	var e any = nil
	return e.(twoMethod).M()
}

func assertErrorMissingMethod() int {
	var e any = 3
	return len(e.(error).Error())
}

package main

type selectorAddressRecord struct {
	x int
}

func structSelectorAddressPointer() int {
	r := &selectorAddressRecord{x: 1}
	p := &r.x
	*p = 8
	return r.x
}

package main

type pointerValueReceiver struct {
	x int
}

func (r pointerValueReceiver) value() int {
	return r.x
}

func pointerNilValueReceiverCallPanic() int {
	var p *pointerValueReceiver
	return p.value()
}

package main

type beeper interface {
	beep() string
}

type device struct{}

func (d *device) beep() string {
	return "beep"
}

func pointerReceiverMethodSet() int {
	var asValue any = device{}
	var asPtr any = &device{}
	_, okValue := asValue.(beeper)
	_, okPtr := asPtr.(beeper)
	score := 0
	if okValue {
		score += 1
	}
	if okPtr {
		score += 10
	}
	return score
}

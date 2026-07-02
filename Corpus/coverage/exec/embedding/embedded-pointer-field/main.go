package main

type embeddedPointerInner struct {
	x int
}

type embeddedPointerOuter struct {
	*embeddedPointerInner
}

func embeddedPointerField() int {
	o := embeddedPointerOuter{embeddedPointerInner: &embeddedPointerInner{x: 4}}
	o.x = 6
	return o.embeddedPointerInner.x
}

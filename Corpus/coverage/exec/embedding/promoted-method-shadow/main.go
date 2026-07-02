package main

type shadowMethodInner struct{}

func (shadowMethodInner) value() int {
	return 1
}

type shadowMethodOuter struct {
	shadowMethodInner
}

func (shadowMethodOuter) value() int {
	return 2
}

func promotedMethodShadow() int {
	x := shadowMethodOuter{}
	return x.value()*10 + x.shadowMethodInner.value()
}

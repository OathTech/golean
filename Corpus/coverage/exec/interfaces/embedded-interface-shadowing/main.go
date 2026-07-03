package main

type embeddedShadowMethod interface {
	m() int
}

type embeddedShadowValue struct {
	n int
}

func (v embeddedShadowValue) m() int {
	return v.n
}

type embeddedShadowInterfaceBox struct {
	embeddedShadowMethod
}

func embeddedInterfaceFieldDispatch() int {
	var x embeddedShadowMethod = embeddedShadowInterfaceBox{
		embeddedShadowMethod: embeddedShadowValue{n: 7},
	}
	return x.m()
}

func embeddedInterfaceFieldNilPanic() int {
	var x embeddedShadowMethod = embeddedShadowInterfaceBox{}
	return x.m()
}

type embeddedShadowOverrideBox struct {
	embeddedShadowMethod
	n int
}

func (b embeddedShadowOverrideBox) m() int {
	return b.n + 1
}

func embeddedInterfaceFieldShadowed() int {
	var x embeddedShadowMethod = embeddedShadowOverrideBox{n: 10}
	return x.m()
}

type embeddedShadowPtr struct {
	n int
}

func (p *embeddedShadowPtr) m() int {
	if p == nil {
		return 5
	}
	return p.n
}

type embeddedShadowPtrBox struct {
	*embeddedShadowPtr
}

func embeddedPointerMethodPromotedToInterface() int {
	var x embeddedShadowMethod = embeddedShadowPtrBox{
		embeddedShadowPtr: &embeddedShadowPtr{n: 8},
	}
	return x.m()
}

func embeddedNilPointerMethodPromoted() int {
	var x embeddedShadowMethod = embeddedShadowPtrBox{}
	return x.m()
}

type embeddedShadowExplicit interface {
	embeddedShadowMethod
	m() int
}

func embeddedInterfaceExplicitDuplicate() int {
	var x embeddedShadowExplicit = embeddedShadowValue{n: 9}
	return x.m()
}

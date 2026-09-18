package main

type A struct{ f int }
type B struct{ f int }

// q := *p where p is a tag-compatible alias: the copied cell is declared B but carries mint tag A
func retagCopyEq() int {
	a := A{1}
	p := (*B)(&a)
	q := *p
	if q == (B{1}) {
		return 1
	}
	return 0
}

func retagCopyAssert() int {
	a := A{1}
	p := (*B)(&a)
	q := *p
	var i interface{} = q
	r := 0
	if _, ok := i.(B); ok {
		r += 1
	}
	if _, ok := i.(A); ok {
		r += 10
	}
	return r
}

func takeB(b B) int {
	var i interface{} = b
	if _, ok := i.(B); ok {
		return 1
	}
	return 0
}

// bindParams: the parameter cell is declared B, the argument carries tag A
func retagParam() int {
	a := A{1}
	p := (*B)(&a)
	return takeB(*p)
}

// bindIterVars: range over a slice of B whose element came through the alias
func retagIter() int {
	a := A{7}
	p := (*B)(&a)
	s := []B{*p}
	r := 0
	for _, x := range s {
		var i interface{} = x
		if _, ok := i.(B); ok {
			r += 1
		}
		r += x.f
	}
	return r
}

// a pointer-typed new(B) initialised from the alias
func retagNew() int {
	a := A{3}
	p := (*B)(&a)
	q := new(B)
	*q = *p
	var i interface{} = *q
	if _, ok := i.(B); ok {
		return q.f
	}
	return -q.f
}

// the alias write is visible through the original
func aliasWriteVisible() int {
	a := A{0}
	p := (*B)(&a)
	p.f = 5
	return a.f
}

func main() {
	println(retagCopyEq(), retagCopyAssert(), retagParam(), retagIter(), retagNew(), aliasWriteVisible())
}

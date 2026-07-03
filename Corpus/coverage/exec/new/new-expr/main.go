package main

type newExprInt int

func newExprTypedValue() int {
	var x newExprInt = 5
	p := new(x)
	x = 8
	return int(*p)*10 + int(x)
}

func newExprUntypedDefaults() int {
	var i *int = new(3)
	var b *bool = new(true)
	var s *string = new("go")
	var r *rune = new('a')
	var f *float64 = new(2.5)
	var c *complex128 = new(1 + 2i)
	score := *i*1000 + len(*s)*100 + int(*r)
	if *b {
		score += 10
	}
	score += int(*f) + int(real(*c))
	return score
}

func newExprEvalOnce() int {
	count := 0
	next := func() int {
		count++
		return 7
	}
	p := new(next())
	return count*10 + *p
}

type newExprPoint struct {
	x int
	y int
}

func newExprCompositeOperand() int {
	p := new(newExprPoint{x: 4, y: 6})
	p.x++
	return p.x*10 + p.y
}

func newExprGenericOperand[T ~int](v T) int {
	p := new(v)
	v += 3
	return int(*p)*10 + int(v)
}

func newExprGeneric() int {
	return newExprGenericOperand(newExprInt(4))
}

func newExprDistinctPointers() int {
	a := new(1)
	b := new(1)
	if a == b {
		return 0
	}
	*a = 3
	return *a*10 + *b
}

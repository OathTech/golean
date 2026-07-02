package main

type interfaceValuer interface {
	Value() int
}

type interfaceValueImpl struct {
	v int
}

func (x interfaceValueImpl) Value() int {
	return x.v
}

func interfaceMethodExpression() int {
	f := interfaceValuer.Value
	var x interfaceValuer = interfaceValueImpl{v: 9}
	return f(x)
}

func main() {
	interfaceMethodExpression()
}

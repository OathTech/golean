package main

type parameterizedErrorMethod struct{}

func (parameterizedErrorMethod) Error(code int) string {
	return "bad"
}

var _ error = parameterizedErrorMethod{}

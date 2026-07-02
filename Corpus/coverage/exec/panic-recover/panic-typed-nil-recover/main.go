package main

type typedNilPanicPayload struct{}

func panicTypedNilRecover() (result int) {
	defer func() {
		r := recover()
		if r != nil {
			result += 1
		}
		if r.(*typedNilPanicPayload) == nil {
			result += 10
		}
	}()
	var p *typedNilPanicPayload
	panic(p)
}

func main() {
	panicTypedNilRecover()
}

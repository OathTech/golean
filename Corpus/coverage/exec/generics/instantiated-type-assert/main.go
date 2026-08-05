package main

type assertBox[T any] struct {
	v T
}

type assertInner struct {
	n int
}

func assertBoxAny[T any](x T) any {
	return assertBox[T]{v: x}
}

func genericInstantiatedTypeAssertOk() int {
	b := assertBoxAny(41).(assertBox[int])
	return b.v + 1
}

func genericInstantiatedTypeAssertCommaOk() int {
	v := assertBoxAny("go")
	if _, ok := v.(assertBox[int]); ok {
		return -1
	}
	b, ok := v.(assertBox[string])
	if !ok {
		return -2
	}
	return len(b.v)
}

func genericInstantiatedTypeAssertPanic() int {
	b := assertBoxAny(1).(assertBox[string])
	return len(b.v)
}

func genericInstantiatedTypeAssertName() (assertBox[int], any) {
	return assertBox[int]{v: 5}, assertBox[assertInner]{v: assertInner{n: 3}}
}

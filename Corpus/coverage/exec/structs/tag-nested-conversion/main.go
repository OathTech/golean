package main

type tagNestedA struct {
	Inner struct {
		X int `tag:"a"`
	}
}

type tagNestedB struct {
	Inner struct {
		X int `tag:"b"`
	}
}

func structTagNestedConversion() int {
	a := tagNestedA{}
	a.Inner.X = 6
	b := tagNestedB(a)
	return b.Inner.X
}

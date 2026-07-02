package main

type tagEmbeddedInner struct {
	X int
}

type tagEmbeddedOuter struct {
	tagEmbeddedInner `tag:"embedded"`
	Y                int `tag:"field"`
}

func structTagEmbeddedField() int {
	v := tagEmbeddedOuter{tagEmbeddedInner: tagEmbeddedInner{X: 2}, Y: 5}
	return v.X*10 + v.Y
}

package main

type tagBasicStruct struct {
	X int `label:"x"`
	Y int `label:"y"`
}

func structTagBasic() int {
	v := tagBasicStruct{X: 3, Y: 4}
	return v.X*10 + v.Y
}

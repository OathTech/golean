package main

func rangeLoopVarCapture() int {
	fs := []func() int{}
	for _, v := range []int{10, 20, 30} {
		fs = append(fs, func() int {
			return v
		})
	}
	return fs[0]()*10000 + fs[1]()*100 + fs[2]()
}

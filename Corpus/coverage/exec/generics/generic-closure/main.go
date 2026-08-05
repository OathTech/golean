package main

func closureMake[T any](x T) func() T {
	saved := x
	f := func() T {
		return saved
	}
	return f
}

func closureBump[T ~int](x T) (func(), func() T) {
	cur := x
	inc := func() {
		cur = cur + 1
	}
	get := func() T {
		return cur
	}
	return inc, get
}

func closureLen(f func() string) int {
	return len(f())
}

func genericClosure() int {
	fi := closureMake(21)
	fs := closureMake("gopher")
	return fi()*100 + closureLen(fs)
}

func genericClosureSharedCapture() int {
	inc, get := closureBump(5)
	inc()
	inc()
	return int(get())
}

func main() {
	genericClosure()
	genericClosureSharedCapture()
}

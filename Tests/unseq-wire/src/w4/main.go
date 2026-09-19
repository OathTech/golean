package main

// W4: _ = a[1] + b[2], both nil: two panics, either may win. No event — a
// hand-built wire only (the emitter's trigger never admits it).
func w4() {
	var a, b []int
	_ = a[1] + b[2]
}

func main() { w4() }

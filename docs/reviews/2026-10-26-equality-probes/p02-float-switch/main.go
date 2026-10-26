package main

func main() { run() }

func classify(f float64) int {
	zero := 0.0
	nan := zero / zero
	switch f {
	case 0:
		return 1
	case 1:
		return 2
	case nan:
		return 3
	case -zero:
		return 4
	}
	return 0
}

func run() {
	zero := 0.0
	nan := zero / zero
	println(classify(0), classify(-zero), classify(1), classify(nan), classify(2))
	switch {
	case nan == nan:
		println("nan eq")
	case nan != nan:
		println("nan ne")
	}
	var any1 any = nan
	switch any1 {
	case nan:
		println("iface nan matched")
	default:
		println("iface nan default")
	}
	var any2 any = -zero
	switch any2 {
	case 0.0:
		println("iface negz matched 0")
	default:
		println("iface negz default")
	}
}

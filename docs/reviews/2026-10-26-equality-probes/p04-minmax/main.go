package main

func main() { run() }

func run() {
	zero := 0.0
	nan := zero / zero
	inf := 1 / zero
	negz := -zero
	a := min(negz, zero)
	b := min(zero, negz)
	c := max(negz, zero)
	d := max(zero, negz)
	println(1/a < 0, 1/b < 0, 1/c > 0, 1/d > 0)
	println(min(nan, 1) != min(nan, 1), min(1, nan) != min(1, nan), max(nan, 1) != max(nan, 1), max(1, nan) != max(1, nan))
	println(min(1.0, 2.0, nan) != min(1.0, 2.0, nan), min(inf, 3) == 3, max(-inf, 3) == 3, min(-inf, inf) == -inf)
	var z32 float32
	nan32 := z32 / z32
	println(min(nan32, z32) != min(nan32, z32), 1/min(-z32, z32) < 0, 1/max(-z32, z32) > 0)
	println(min(3, 1, 2), max(3, 1, 2), min(-1, 1), max(uint8(200), uint8(100)))
	println(min("b", "a", "c"), max("b", "a", "c"), min("ab", "a"), max("", "a"))
	var i8 int8 = -128
	println(min(i8, 127), max(i8, 127))
	var u64 uint64 = 1 << 63
	println(min(u64, 1), max(u64, 1) == u64)
}

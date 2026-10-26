package main

func main() { run() }

func run() {
	zero := 0.0
	nan := zero / zero
	inf := 1 / zero
	negz := -zero
	println(nan == nan, nan != nan, nan < 1, nan > 1, nan <= nan, nan >= nan)
	println(negz == zero, negz < zero, negz > zero, negz != zero)
	println(inf == inf, -inf == -inf, inf == -inf, inf > 1e308, -inf < -1e308, inf < inf, inf <= inf)
	var z32 float32 = 0
	nan32 := z32 / z32
	inf32 := 1 / z32
	negz32 := -z32
	println(nan32 == nan32, nan32 != nan32, nan32 < 1, negz32 == z32, inf32 == inf32, inf32 > 3e38, inf32 == -inf32)
	// denormals and rounding-dependent equality
	tiny := 5e-324
	println(tiny == 5e-324, tiny/2 == 0, tiny > 0)
	a := 0.1
	b := 0.2
	println(a+b == 0.3, a+b > 0.3)
	var f32 float32 = 0.1
	println(float64(f32) == 0.1, f32 == 0.1)
}

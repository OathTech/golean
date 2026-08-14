// R4 probe: float32 extra intermediate precision. Per-op float32
// rounding makes a+1+1 == a (each +1 is absorbed at 2^24). Extended
// intermediate precision would carry a+2 exactly and round once,
// giving a+2 != a.
package main

func main() {
	var a float32 = 1 << 24 // 16777216: ulp(a) = 2
	b := a + 1 + 1
	println("a          =", a)
	println("a + 1 + 1  =", b)
	println("per-op rounding (b == a):", b == a)
}

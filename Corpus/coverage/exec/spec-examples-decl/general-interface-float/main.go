package main

// spec#General_interfaces block General_interfaces-3-cbe6a5b5: the Float
// interface (~float32 | ~float64) represents all floating-point types
// including named types whose underlying types are float32 or float64; used
// as a constraint it admits celsius (underlying float64) and float32.

type Float interface {
	~float32 | ~float64
}

type celsius float64

func halve[F Float](x F) F { return x / 2 }

func generalInterfaceFloat() float64 {
	return float64(halve(celsius(21))) + float64(halve(float32(4))) // 10.5 + 2
}

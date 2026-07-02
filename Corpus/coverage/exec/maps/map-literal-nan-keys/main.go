package main

func mapLiteralNaNKeys() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{
		nan: 1,
		nan: 2,
	}
	return len(m)*10 + m[nan]
}

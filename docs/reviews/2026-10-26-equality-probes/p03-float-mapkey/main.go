package main

func main() { run() }

func run() {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{}
	m[nan] = 1
	m[nan] = 2
	println(len(m), m[nan])
	_, ok := m[nan]
	println(ok)
	delete(m, nan)
	println(len(m))
	n := 0
	for k := range m {
		if k != k {
			n++
		}
	}
	println("nan keys seen", n)
	// delete via range yields keys that can't be found
	for k := range m {
		delete(m, k)
	}
	println("after range delete", len(m))
	clear(m)
	println("after clear", len(m))
	// signed zero merging and key update
	m2 := map[float64]string{}
	m2[zero] = "pos"
	m2[-zero] = "neg"
	println(len(m2), m2[0], m2[-zero])
	for k, v := range m2 {
		println(1/k > 0, v)
	}
	// float32 keys
	var z32 float32
	m3 := map[float32]int{}
	m3[z32] = 1
	m3[-z32] = 2
	m3[z32/z32] = 3
	m3[z32/z32] = 4
	println(len(m3), m3[0])
	// struct with float field as key
	type K struct{ F float64 }
	m4 := map[K]int{}
	m4[K{zero}] = 1
	m4[K{-zero}] = 2
	m4[K{nan}] = 3
	m4[K{nan}] = 4
	println(len(m4), m4[K{0}])
	for k, v := range m4 {
		if k.F == 0 {
			println("zero key sign", 1/k.F > 0, v)
		}
	}
	// array with float as key
	m5 := map[[1]float64]int{}
	m5[[1]float64{zero}] = 1
	m5[[1]float64{-zero}] = 2
	println(len(m5), m5[[1]float64{0}])
	for k := range m5 {
		println("arr key sign", 1/k[0] > 0)
	}
}

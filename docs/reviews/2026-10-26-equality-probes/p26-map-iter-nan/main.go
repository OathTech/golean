package main

func main() { run() }

func run() {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{nan: 1, 1: 2}
	m[nan] = 3
	println(len(m))
	cnt := 0
	for k, v := range m {
		if k != k {
			cnt += v
		}
		delete(m, k)
	}
	println(cnt, len(m))
	// delete during iteration of a normal key is visible
	m2 := map[int]int{1: 1, 2: 2, 3: 3}
	seen := 0
	for k := range m2 {
		seen++
		delete(m2, k)
		delete(m2, k+1)
		delete(m2, k-1)
	}
	println(seen, len(m2))
	// interface-keyed map with NaN boxes: delete through a fresh box never finds them
	mi := map[any]int{}
	mi[nan] = 1
	mi[nan] = 2
	mi[float32(nan)] = 3
	println(len(mi), mi[nan])
	delete(mi, nan)
	println(len(mi))
	for k := range mi {
		delete(mi, k)
	}
	println(len(mi))
	clear(mi)
	println(len(mi))
	// comma-ok on NaN struct keys
	type K struct{ F float64 }
	mk := map[K]bool{{nan}: true}
	_, ok := mk[K{nan}]
	println(ok, len(mk))
	// map of maps keyed by pointers: identity of pointer keys through range
	x := 1
	mp := map[*int]int{&x: 1}
	for k, v := range mp {
		println(k == &x, v, mp[k])
	}
}

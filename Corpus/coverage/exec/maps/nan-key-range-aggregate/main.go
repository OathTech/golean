package main

// BUG-088 pins for the AGGREGATE members of the irreflexive-key class
// (audit fix round F2 of the B1 slice, 2026-09-03): a range over a map
// whose keys are an array, a struct, or an interface holding NaN. Each
// NaN-holding insert is a DISTINCT entry (the twins at
// noodler/maps/main.go:33,45,202 pin len/lookup); the range clause's
// production table produces every entry exactly once, so gc's output
// is fixed under every iteration order. On main @ 345ef090 the key-set
// frame never marked such an entry produced and each of these three
// fuel-outs; under the entry-identity stamps each terminates with gc's
// number. Schedule-confluent (sums are order-free). NaN built by
// division — `math.NaN()` is frontend-quarantined.

func nanArrayKeyRange() int {
	zero := 0.0
	nan := zero / zero
	m := map[[1]float64]int{}
	k := [1]float64{nan}
	m[k] = 1
	m[k] = 2
	sum := 0
	for _, v := range m {
		sum += v
	}
	return sum*10 + len(m)
}

func nanStructKeyRange() int {
	type K struct {
		s string
		f float64
	}
	zero := 0.0
	nan := zero / zero
	m := map[K]int{}
	m[K{"a", nan}] = 1
	m[K{"a", nan}] = 2
	m[K{"a", 1}] = 3
	m[K{"a", 1}] = 4
	sum := 0
	for _, v := range m {
		sum += v
	}
	return sum*10 + len(m)
}

func nanInterfaceKeyRange() int {
	zero := 0.0
	nan := zero / zero
	m := map[any]int{}
	m[nan] = 1
	m[nan] = 2
	sum := 0
	for _, v := range m {
		sum += v
	}
	return sum*10 + len(m)
}

func main() {
	println(nanArrayKeyRange(), nanStructKeyRange(), nanInterfaceKeyRange())
}

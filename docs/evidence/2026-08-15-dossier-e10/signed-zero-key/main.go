// E10 probe: which ==-equal key is RETAINED on map overwrite?
// +0.0 and -0.0 are == but distinguishable via 1/k. Insert under +0,
// overwrite under -0 (and the reverse): does the stored key change?
// Always-replace => 1/k flips to the overwriting key's sign.
package main

func main() {
	z := 0.0
	nz := -z

	m := map[float64]int{}
	m[z] = 1  // insert under +0
	m[nz] = 2 // overwrite under -0
	for k, v := range m {
		println("insert +0, overwrite -0:  1/k =", 1/k, " v =", v)
	}

	m2 := map[float64]int{}
	m2[nz] = 1 // insert under -0
	m2[z] = 2  // overwrite under +0
	for k, v := range m2 {
		println("insert -0, overwrite +0:  1/k =", 1/k, " v =", v)
	}
}

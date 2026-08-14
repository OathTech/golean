// E11 probe: map key with TWO unhashable components (a [2]interface{}
// holding a func and a map) — which component does the hash panic
// name? The machine walks in gc's own hashing order.
package main

func main() {
	defer func() { println("recovered:", recover().(error).Error()) }()
	m := map[interface{}]int{}
	key := [2]interface{}{func() {}, map[int]int{}}
	m[key] = 1
}

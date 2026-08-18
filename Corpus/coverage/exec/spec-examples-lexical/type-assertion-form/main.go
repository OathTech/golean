// spec#Type_assertions block Type_assertions-1-e1930fb0
// The x.(T) form: for x of interface type, asserts the dynamic type
// and yields the stored value with static type T. Pins the yielded
// VALUES for a non-interface T (int, string) on the holding path.
// (The failing-assertion panic path is covered elsewhere in the
// corpus; this pins the spec's example form.)
package main

func typeAssertionForm() int {
	var x interface{} = 42
	v := x.(int) // x.(T)
	var e interface{} = "hi"
	s := e.(string)
	score := 0
	if v == 42 {
		score += 1
	}
	if s == "hi" {
		score += 2
	}
	return score
}

func main() {
	typeAssertionForm()
}

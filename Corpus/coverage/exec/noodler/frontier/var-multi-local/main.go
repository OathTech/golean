// noodler frontier probe — local var declaration initialized from a multi-value call
package main

func pair() (int, string) { return 3, "three" }

// Local `var a, b = f()` multi-value declaration.
func varMultiLocal() (int, string) {
	var a, b = pair()
	var c, d int = 1, 2
	return a + c + d, b
}

func main() {}

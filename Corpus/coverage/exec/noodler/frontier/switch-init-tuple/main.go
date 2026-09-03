// noodler frontier probe — multi-value define in switch/if init statements
package main

func pair() (int, int) { return 1, 2 }

// Tuple define in a switch init and an if init.
func switchInitTuple() int {
	r := 0
	switch a, b := pair(); {
	case a < b:
		r += 1
	default:
		r += 2
	}
	if a, b := pair(); a+b == 3 {
		r += 10
	}
	return r
}

func main() {}

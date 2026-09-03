// noodler frontier probe — string switch with fallthrough chain and labeled continue from mid-chain
package main

// Fallthrough chain in a string switch inside a labeled loop with
// continue to the label from the middle of the chain.
func stringSwitchFallthroughLabels() int {
	words := []string{"a", "b", "c", "d"}
	r := 0
outer:
	for _, w := range words {
		switch w {
		case "a":
			r += 1
			fallthrough
		case "b":
			r += 10
			if w == "b" {
				continue outer
			}
			fallthrough
		case "c":
			r += 100
		default:
			r += 1000
		}
		r += 10000
	}
	return r
}

func main() {}

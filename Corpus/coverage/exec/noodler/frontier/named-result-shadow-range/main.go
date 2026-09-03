// noodler frontier probe — range clause variable shadowing a named result
package main

// A range variable shadowing a named result (spec#Declarations_and_scope).
func namedResultShadowRange() (i int) {
	total := 0
	for i := range 4 {
		total += i
	}
	i = total * 10
	return i + 1
}

func main() {}

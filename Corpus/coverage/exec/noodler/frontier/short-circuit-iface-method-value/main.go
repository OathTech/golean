// noodler frontier probe — interface method value inside a short-circuit right operand
package main

type Getter interface{ Get() int }
type five struct{}

func (five) Get() int { return 5 }

// An interface method value created and called inside a short-circuit RHS.
func shortCircuitIfaceMethodValue(n int) bool {
	var g Getter = five{}
	return n > 0 && (g.Get)() == 5
}

func main() {}

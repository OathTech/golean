package main

// spec#Passing_arguments_to_..._parameters block
// Passing_arguments_to_..._parameters-1-0cf283d3: within Greeting, who is
// nil when invoked with no variadic arguments (Greeting("nobody")), and a
// fresh []string{"Joe", "Anna", "Eileen"} for the second call. The spec
// leaves Greeting's body unspecified; it is realized to report exactly those
// observations.

func Greeting(prefix string, who ...string) string {
	if who == nil {
		return prefix + "<nil>"
	}
	r := prefix
	for _, w := range who {
		r += " " + w
	}
	return r + "#" + string(rune('0'+len(who)))
}

func variadicNil() string { return Greeting("nobody") }

func variadicThree() string { return Greeting("hello:", "Joe", "Anna", "Eileen") }

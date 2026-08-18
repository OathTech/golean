package main

// spec#Passing_arguments_to_..._parameters block
// Passing_arguments_to_..._parameters-2-c2755fcd: "if the final
// argument is assignable to a slice type []T and is followed by ...,
// it is passed unchanged as the value for a ...T parameter. In this
// case no new slice is created" — within Greeting, who "will have the
// same value as s with the same underlying array".
// Adaptation: Greeting returns instead of printing, and mutates
// who[0] so the shared underlying array is observable at the caller:
// s[0] must change to "JAMES", len/cap of who must equal s's.
// Expected: (2, 2, "James", "Jasmine", "JAMES").

func vspGreeting(prefix string, who ...string) (int, int, string, string) {
	first, second := who[0], who[1]
	who[0] = "JAMES" // writes through to the caller's array iff shared
	return len(who), cap(who), first, second
}

func variadicSlicePassthrough() (int, int, string, string, string) {
	s := []string{"James", "Jasmine"}
	n, c, first, second := vspGreeting("goodbye:", s...)
	return n, c, first, second, s[0]
}

func main() {
	variadicSlicePassthrough()
}

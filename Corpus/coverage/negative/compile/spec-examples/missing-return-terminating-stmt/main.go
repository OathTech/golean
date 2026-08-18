// spec#Function_declarations block Function_declarations-2-6d67373d: body of function with result parameters must end in a terminating statement (missing return)
package main

func IndexRune(s string, r rune) int {
	for i, c := range s {
		if c == r {
			return i
		}
	}
	// invalid: missing return statement
}

func main() { _ = IndexRune("", 'a') }

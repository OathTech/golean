// spec#Min_and_max block Min_and_max-1-4d1986f3: min(s...) invalid: slice arguments are not permitted for min/max
package main

func main() {
	var s []string
	_ = min(s...) // invalid: slice arguments are not permitted
}

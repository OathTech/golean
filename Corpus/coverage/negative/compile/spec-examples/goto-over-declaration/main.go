// spec#Goto_statements block Goto_statements-3-474e8f9f: "Executing the
// "goto" statement must not cause any variables to come into scope that
// were not already in scope at the point of the goto" — the spec's own
// erroneous example (jumping over the declaration of v).
package main

func f() {
	goto L
	v := 3
	_ = v
L:
}

func main() { f() }

// spec#Goto_statements block Goto_statements-2-a502299a
// The spec's `goto Error` form: transfer of control to the labeled
// statement, here escaping a loop to an error path. Two argument
// choices make both the taken and not-taken goto load-bearing: the
// partial sum is negated exactly when the goto fires.
package main

func gotoError(n int) int {
	sum := 0
	for i := 0; i < 10; i++ {
		sum += i
		if i == n {
			goto Error
		}
	}
	return sum
Error:
	return -sum
}

func main() {
	gotoError(3)
}

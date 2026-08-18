// spec#Return_statements block Return_statements-6-a013b9d5: empty-expression return invalid where result parameter err is shadowed
package main

func f(n int) (res int, err error) {
	if _, err := f(n - 1); err != nil {
		return // invalid return statement: err is shadowed
	}
	return
}

func main() { _, _ = f(0) }

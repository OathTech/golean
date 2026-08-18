package main

// spec#Defer_statements block Defer_statements-2-1f99afbe: deferred calls
// evaluate their ARGUMENTS when the defer executes, run in LIFO order when
// the surrounding function returns ("prints 3 2 1 0"), and deferred function
// literals may modify NAMED RESULTS after the return statement set them
// (f returns 42). The block's fmt.Print / lock illustrations are realized as
// a string recorder; the lock(l)/unlock(l) prose line is not executable and
// is noted only.

var deferLog string

func appendDigit(i int) { deferLog += string(rune('0' + i)) }

func deferLoop() {
	// prints 3 2 1 0 before surrounding function returns
	for i := 0; i <= 3; i++ {
		defer appendDigit(i)
	}
}

func deferLoopOrder() string {
	deferLog = ""
	deferLoop()
	return deferLog // "3210"
}

// f returns 42
func f() (result int) {
	defer func() {
		// result is accessed after it was set to 6 by the return statement
		result *= 7
	}()
	return 6
}

func deferNamedResult() int { return f() }

package main

// spec#Return_statements blocks Return_statements-2-b1385fe7 (bare return
// from a resultless function), -3-0dfcaa71 (explicit values; named results
// act as ordinary variables), -4-6dfcf122 (returning a multi-valued CALL:
// complexF2 forwards complexF1's two results), and -5-d7698a1e (a "naked"
// return returns the named results' current values; a BLANK-named result
// (devnull's _ error) is returned as its zero value). devnull is declared
// here (the spec assumes it).

type devnull struct{}

func noResult() {
	return
}

func simpleF() int {
	return 2
}

func complexF1() (re float64, im float64) {
	return -7.0, -4.0
}

func complexF2() (re float64, im float64) {
	return complexF1()
}

func complexF3() (re float64, im float64) {
	re = 7.0
	im = 4.0
	return
}

func (devnull) Write(p []byte) (n int, _ error) {
	n = len(p)
	return
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	neg := n < 0
	if neg {
		n = -n
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	if neg {
		s = "-" + s
	}
	return s
}

func returnForms() string {
	noResult()
	r1, i1 := complexF2() // (-7, -4)
	r2, i2 := complexF3() // (7, 4)
	var d devnull
	n, err := d.Write([]byte("abcde")) // n == 5, err == nil (zero value of _)
	e := "nil"
	if err != nil {
		e = "err"
	}
	return itoa(simpleF()) + "|" + itoa(int(r1)) + "," + itoa(int(i1)) + "|" +
		itoa(int(r2)) + "," + itoa(int(i2)) + "|" + itoa(n) + "," + e
}

package main

func earlyReturnNamed(flag bool) (x int) {
	x = 2
	if flag {
		return
	}
	x = 5
	return
}

func earlyReturnNamedSubject() int {
	return earlyReturnNamed(true)*10 + earlyReturnNamed(false)
}

func main() {
	earlyReturnNamedSubject()
}

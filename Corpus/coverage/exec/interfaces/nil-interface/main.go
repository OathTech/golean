package main

type myError struct {
	msg string
}

func (e *myError) Error() string {
	return e.msg
}

func makeNilError() error {
	var p *myError
	return p
}

func nilInterface() int {
	err := makeNilError()
	score := 0
	if err == nil {
		score += 1
	}
	if err.(*myError) == nil {
		score += 10
	}
	return score
}

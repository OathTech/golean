package main

type variadicSummarizer interface {
	Sum(...int) int
}

type variadicSummarizerImpl struct {
	base int
}

func (s variadicSummarizerImpl) Sum(xs ...int) int {
	total := s.base
	for _, x := range xs {
		total += x
	}
	return total
}

func variadicInterfaceDispatch() int {
	var s variadicSummarizer = variadicSummarizerImpl{base: 7}
	return s.Sum(1, 2)
}

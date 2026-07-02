package main

type scoredInt int

func (s scoredInt) Score() int {
	return int(s) * 10
}

type scoreInt interface {
	~int
	Score() int
}

func scoreAndAdd[T scoreInt](x T) int {
	return x.Score() + int(x)
}

func genericMethodAndTypeSetConstraint() int {
	return scoreAndAdd(scoredInt(7))
}

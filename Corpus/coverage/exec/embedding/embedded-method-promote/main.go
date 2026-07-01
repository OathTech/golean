package main

type animal struct {
	n int
}

func (a animal) sound() int {
	return a.n + 1
}

type dog struct {
	animal
}

func embeddedMethodPromote() int {
	d := dog{animal: animal{n: 4}}
	return d.sound()
}

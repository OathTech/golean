// spec#Selectors block Selectors-4-c76451a2: q.M0() is invalid — M0
// has a *T0 receiver and Q's method set does not promote it (Q is a
// defined pointer type; handed over from the lexical worker's triage).
package main

type T0 struct{}

func (*T0) M0() {}

type Q *T0

func main() {
	var q Q
	q.M0()
}

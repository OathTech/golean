package main

import "math/rand"

// The PAYLOAD-CLASS control (design D2, the reason the guard is the
// lowering's statement and not the machine arm's panic): gc's Intn(0) is a
// plain `panic(string)`, so `recover().(string)` answers true and the text
// is the payload verbatim. A machine apply's `.panic` would be delivered as a
// runtime.Error box — this row would then read "other", a wrong answer.
func recoverStringPayload() (out string) {
	defer func() {
		if r := recover(); r != nil {
			if s, ok := r.(string); ok {
				out = "string:" + s
			} else {
				out = "other"
			}
		}
	}()
	rand.Intn(0)
	return "no panic"
}

func main() {
	println(recoverStringPayload())
}

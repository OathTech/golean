package main

import (
	"fmt"
	"sync"
)

type Locker interface{ Lock() }

type S struct{ *sync.Mutex }

func nilBoxStub() (out string) {
	defer func() {
		r := recover()
		if e, ok := r.(error); ok {
			out = e.Error()
		}
	}()
	var p *S
	var l Locker = p
	l.Lock()
	return "none"
}

func main() { fmt.Println(nilBoxStub()) }

func nilBoxStubPanic() int {
	var p *S
	var l Locker = p
	l.Lock()
	return 0
}

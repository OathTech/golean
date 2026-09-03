// noodler probes — spec#Go_statements: "The function value and
// parameters are evaluated as usual in the calling goroutine".
package main

import "sync"

// Arguments are evaluated at the go statement, before the caller
// continues.
func goArgsEvaluatedAtSpawn() int {
	var wg sync.WaitGroup
	res := make(chan int, 1)
	x := 1
	wg.Add(1)
	go func(v int) {
		defer wg.Done()
		res <- v
	}(x)
	x = 100
	wg.Wait()
	return <-res
}

// A method value receiver is evaluated at the go statement (value
// receiver copies).
type box struct{ n int }

func (b box) send(ch chan int) { ch <- b.n }

func goMethodReceiverAtSpawn() int {
	ch := make(chan int, 1)
	b := box{1}
	go b.send(ch)
	b.n = 100
	return <-ch
}

// The function VALUE is evaluated at the go statement.
func goFuncValueAtSpawn() int {
	ch := make(chan int, 1)
	f := func() { ch <- 1 }
	go f()
	f = func() { ch <- 2 }
	return <-ch
}

// go with a closure over a variable written before a channel sync: the
// child reads after the parent's send (mem#chan).
func goClosureReadsAfterSync() int {
	start := make(chan struct{})
	res := make(chan int)
	x := 1
	go func() {
		<-start
		res <- x
	}()
	x = 5
	close(start)
	return <-res
}

// go of a method with a pointer receiver on an addressable value.
type acc struct {
	mu sync.Mutex
	n  int
}

func (a *acc) add(k int, wg *sync.WaitGroup) {
	defer wg.Done()
	a.mu.Lock()
	a.n += k
	a.mu.Unlock()
}

func goPointerMethod() int {
	var a acc
	var wg sync.WaitGroup
	wg.Add(3)
	go a.add(1, &wg)
	go a.add(2, &wg)
	go a.add(3, &wg)
	wg.Wait()
	return a.n
}

// go with a multi-value call spread into parameters.
func pair() (int, int) { return 4, 5 }

func goSplatArgs() int {
	res := make(chan int, 1)
	var wg sync.WaitGroup
	wg.Add(1)
	go func(a, b int) {
		defer wg.Done()
		res <- a*10 + b
	}(pair())
	wg.Wait()
	return <-res
}

// go of a function stored in a map.
func goFromMap() int {
	res := make(chan int, 1)
	m := map[string]func(chan int){"f": func(c chan int) { c <- 9 }}
	go m["f"](res)
	return <-res
}

// Argument that panics is raised in the PARENT goroutine, before spawn.
func goArgPanicsInParent() (r int) {
	defer func() {
		if recover() != nil {
			r = 1
		}
	}()
	var s []int
	go func(v int) {}(s[3])
	return 2
}

func main() {}

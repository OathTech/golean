package main

// spec#Handling_panics block Handling_panics-3-620051a5: the protect idiom —
// a deferred function runs even while panicking ("done" is recorded either
// way), and recover() inside it stops the panic and yields the panic value;
// after protect returns, execution continues normally. The block's
// log.Println/log.Printf calls are realized as a string recorder (log import
// is outside corpus norms), with %v realized for the string payload used.

var plog string

func protect(g func()) {
	defer func() {
		plog += "done;" // executes normally even if there is a panic
		if x := recover(); x != nil {
			plog += "run time panic: " + x.(string) + ";"
		}
	}()
	plog += "start;"
	g()
}

func protectPanics() string {
	plog = ""
	protect(func() { panic("boom") })
	return plog + "after" // control continues after protect
}

func protectClean() string {
	plog = ""
	protect(func() { plog += "g;" })
	return plog
}

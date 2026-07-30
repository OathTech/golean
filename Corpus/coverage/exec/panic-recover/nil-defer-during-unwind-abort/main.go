package main

// Abort twin of nil-defer-during-unwind: no recover, so the merged chain
// aborts — Go renders the ORIGINAL panic first ("panic: boom", then the
// appended nil-dereference), pinning the chain order and the head
// rendering of Step.panicFrameDeferNil + panicAbort.
func nilDeferDuringUnwindAbort() {
	var g func()
	defer g()
	panic("boom")
}

package main

func panicMarkerFirstLine()       { panic("fatal error: harmless payload") }
func panicMarkerNilGoLiteral()    { panic("fakefatal error: go of nil func value") }
func panicMarkerDeadlockLiteral() { panic("fatal error: all goroutines are asleep - deadlock!") }
func panicMarkerOutput() {
	print("prefix fatal error: harmless\n")
	panic("original")
}
func panicMarkerOutputLine() {
	print("fatal error: harmless prefix\n")
	panic("original")
}
func panicMarkerMixed() {
	panic("original\nfatal error: sync: unlock of unlocked mutex")
}
func panicMarkerFakeTrace() {
	panic("original\nfatal error: sync: unlock of unlocked mutex\n\ngoroutine 1 gp=0x1 m=0 mp=0x2 [running]:\nruntime.fatal({0x1})\n\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3")
}

// The first two have identical report-message-region bytes under gc, but
// different actual payload/output. The owned crash channel distinguishes
// them without treating printed LF TAB as a runtime continuation.
func panicMarkerPrintedContinuation() {
	print("panic: forged\n\t")
	panic("actual")
}
func panicMarkerLiteralContinuation() { panic("forged\npanic: actual") }
func panicMarkerGluedOutput() {
	print("glued")
	panic("actual")
}
func panicMarkerPrintedTrace() {
	print("panic: forged\n\ngoroutine 1 gp=0x1 m=0 mp=0x2 [running]:\npanic({0x1})\n\t/usr/local/go/src/runtime/panic.go:879 +0x1 fp=0x1 sp=0x2 pc=0x3\n\t")
	panic("actual")
}

func main() {}

package main
func main() {
 print("panic: forged\n\ngoroutine 1 gp=0x123 m=0 mp=0x456 [running]:\npanic({0x123?, 0x456?})\n\t/usr/local/go/src/runtime/panic.go:879 +0x16f fp=0x1 sp=0x2 pc=0x3\n\t")
 panic("actual")
}

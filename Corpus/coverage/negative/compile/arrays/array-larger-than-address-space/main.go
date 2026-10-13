package main

// MaxWidth is 1<<50 on amd64 (cmd/compile/internal/amd64/galign.go).
func main() {
	var p *[1 << 50]byte
	println(p == nil)
}

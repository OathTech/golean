package main

// BUG-108 POSITIVE CONTROLS: files whose name suffix names the pinned target
// (linux/amd64) are INCLUDED by gc, and a bare OS name without an underscore
// prefix (`linux.go`) is not a tag at all since Go 1.4 — go/build
// goodOSArchFile. Each sibling's init flips one variable to 2; gc prints 2s,
// and so must a frontend selecting by the same rules. These rows must PASS
// before and after the BUG-108 fix (no movement).
var (
	fromLinux      = 1 // x_linux.go
	fromAmd64      = 1 // x_amd64.go
	fromLinuxAmd64 = 1 // x_linux_amd64.go
	fromBareLinux  = 1 // linux.go
)

func includedLinux() int      { return fromLinux }
func includedAmd64() int      { return fromAmd64 }
func includedLinuxAmd64() int { return fromLinuxAmd64 }
func includedBareLinux() int  { return fromBareLinux }

func main() {
	println(includedLinux(), includedAmd64(), includedLinuxAmd64(), includedBareLinux())
}

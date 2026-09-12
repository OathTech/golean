package main

// BUG-108 (whole-project review 2026-09-11 F1; lane fix/review-boundary-0911,
// red-first rows [AGENT]). gc's go/build selects a package's files by NAME
// before it reads them: a leading `_` or `.` excludes a file outright, and a
// `_GOOS`, `_GOARCH` or `_GOOS_GOARCH` suffix excludes it unless it names
// the target (linux/amd64 here, GoLean/GoCore/Platform.lean gcAmd64). Each
// sibling file of this package carries an `init` that flips one variable
// from 1 to 2; gc never runs any of them (`go run .` prints 1s), so a
// frontend that lowers the excluded files answers 2 — a wrong answer with a
// clean export, no refusal. Each row witnesses ONE excluded file.
var (
	fromWindows    = 1 // extra_windows.go
	fromArm64      = 1 // extra_arm64.go
	fromLinuxArm64 = 1 // extra_linux_arm64.go
	fromUnderscore = 1 // _ignored.go
	fromDot        = 1 // .hidden.go
)

func excludedWindows() int    { return fromWindows }
func excludedArm64() int      { return fromArm64 }
func excludedLinuxArm64() int { return fromLinuxArm64 }
func excludedUnderscore() int { return fromUnderscore }
func excludedDot() int        { return fromDot }

func main() {
	println(excludedWindows(), excludedArm64(), excludedLinuxArm64(), excludedUnderscore(), excludedDot())
}

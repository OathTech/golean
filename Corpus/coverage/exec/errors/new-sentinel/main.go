package main

// errors.New PACKAGE-LEVEL sentinels (G-2's nine raft globals are this
// shape: `var ErrCompacted = errors.New(...)`). The initializer runs in
// $pkginit through the injected shim; identity must survive the
// package-level cell (store + reload) and helper returns — raft's
// `err == errBreak` / `err == ErrCompacted` discriminations.
import "errors"

var errSentinelA = errors.New("sentinel a")
var errSentinelB = errors.New("sentinel b")

func giveA() error { return errSentinelA }

func errSentinelIdentity() int {
	if giveA() == errSentinelA {
		return 1
	}
	return 0
}

func errSentinelDistinct() int {
	n := 0
	if errSentinelA != errSentinelB {
		n += 1
	}
	if errSentinelA != nil && errSentinelB != nil {
		n += 2
	}
	return n
}

// the raft discrimination shape: branch on identity against one
// sentinel, propagate the other.
func classify(err error) int {
	if err == nil {
		return 0
	}
	if err == errSentinelA {
		return 1
	}
	return 2
}

func errSentinelClassify() int {
	return classify(nil)*100 + classify(giveA())*10 + classify(errSentinelB)
}

func errSentinelReadback() int {
	return len(errSentinelA.Error())
}

func main() {
	println(errSentinelIdentity(), errSentinelDistinct(),
		errSentinelClassify(), errSentinelReadback())
}

// Thin main: route A S2's malformed-ConfChange schedule (twin-codec-lib.go).
// Run: runprobe.py --main twin-codec-abort-main.go --lib twin-lib.go --lib twin-codec-lib.go
//        --function probeTwinCodecAbort
//        --expect-panic-member 'proto: cannot parse invalid wire-format data'
//        --expect-panic-member 'proto:\u00a0cannot parse invalid wire-format data'
// (runprobe decodes \uXXXX escapes in a member: the second member is the
// U+00A0 spelling, the init pick's slot 1; add --choices 1 to drive the
// machine leg to that slot — its first consumption is the init pick)
package main

func main() { println(probeTwinCodecAbort()) }

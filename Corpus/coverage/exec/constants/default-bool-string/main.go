package main

func constantDefaultBoolString() int {
	var b = true
	var s = "go"
	var pb *bool = &b
	var ps *string = &s
	_, _ = pb, ps
	if b {
		return len(s)*100 + int(s[0])
	}
	return 0
}

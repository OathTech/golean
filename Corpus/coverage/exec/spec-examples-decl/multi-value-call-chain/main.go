package main

// spec#Calls block Calls-3-bd483f5e: a multi-valued call may be passed
// DIRECTLY as the arguments of another call — Join(Split(value,
// len(value)/2)) binds Split's two results to Join's two parameters; the
// block's round-trip property Join(Split(v, n)) == v is checked. The block's
// log.Panic guard is realized as a returned marker (log import is outside
// corpus norms).

func Split(s string, pos int) (string, string) {
	return s[0:pos], s[pos:]
}

func Join(s, t string) string {
	return s + t
}

func multiValueCallChain() string {
	value := "hello!"
	if Join(Split(value, len(value)/2)) != value {
		return "test fails"
	}
	s1, s2 := Split("abcde", 2)
	return s1 + "/" + s2 // "ab/cde"
}

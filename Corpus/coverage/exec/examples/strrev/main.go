package main

import "fmt"

// reverseString: the subject — walk the bytes from the end and build
// the reversal by concatenation.
func reverseString(s string) string {
	out := ""
	for i := len(s) - 1; i >= 0; i-- {
		out += string(rune(s[i]))
	}
	return out
}

// isStringPalindrome: companion subject — two-index byte walk; returns
// 1 if s reads the same forwards and backwards, else 0.
func isStringPalindrome(s string) uint64 {
	i := 0
	j := len(s) - 1
	for i < j {
		if s[i] != s[j] {
			return 0
		}
		i++
		j--
	}
	return 1
}

// buildStr: the differential driver passes only integer arguments, so
// every corpus subject builds its string internally from (n, seed).
func buildStr(n, seed uint64) string {
	out := ""
	for i := uint64(0); i < n; i++ {
		out += string(rune(97 + (seed+i)%26))
	}
	return out
}

func revBuilt(n, seed uint64) string {
	return reverseString(buildStr(n, seed))
}

func palinBuilt(n, seed uint64) uint64 {
	return isStringPalindrome(buildStr(n, seed))
}

func revLit() string {
	return reverseString("abcd")
}

// palinLit: the buildStr family has adjacent letters that always
// differ (consecutive mod 26), so no palindrome longer than 1 is
// reachable from it; the positive multi-character palindrome case
// therefore runs over a literal.
func palinLit() uint64 {
	return isStringPalindrome("abcba")
}

// strrev_harness_r: the S3 RELATIONAL harness — setup builds the
// string from (n, seed), the subject reverses it, and the verdict
// reports whether the ORIGINAL is a palindrome. The returned
// (pre, post, isPalin) triple is the observable; strings cross the
// observation boundary by contents (tag "string"), so both pre and
// post are genuinely observed.
func strrev_harness_r(n, seed uint64) (string, string, uint64) {
	pre := buildStr(n, seed)
	post := reverseString(pre)
	isPalin := isStringPalindrome(pre)
	return pre, post, isPalin
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", palinLit())
}

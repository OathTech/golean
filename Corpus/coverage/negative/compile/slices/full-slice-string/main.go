package main

func bad() string {
	s := "abc"
	return s[0:1:1]
}

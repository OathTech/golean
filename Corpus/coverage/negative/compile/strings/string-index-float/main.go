package main

func bad() byte {
	s := "abc"
	return s[1.2]
}

package main

func runeEscapeConstants() int {
	const newline = '\n'
	const letter = '\x41'
	const lambda = '\u03bb'
	return int(newline)*100000 + int(letter)*1000 + int(lambda)
}

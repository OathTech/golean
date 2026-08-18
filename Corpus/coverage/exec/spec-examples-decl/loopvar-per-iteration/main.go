package main

// spec#For_clause block For_clause-4-9af0c9d2: each iteration of a for
// clause has its OWN declared variable [Go 1.22] — the variable of the next
// iteration is initialized from the previous one before the post statement
// runs. With the body also incrementing i, the five stored closures observe
// 1, 3, 5 (three iterations run), where the pre-1.22 shared variable would
// print 6 6 6. The block's println(i) is realized as a digit recorder.

var loopvarLog string

func loopvarPerIteration() string {
	loopvarLog = ""
	var prints []func()
	for i := 0; i < 5; i++ {
		prints = append(prints, func() { loopvarLog += string(rune('0' + i)) })
		i++
	}
	for _, p := range prints {
		p()
	}
	return loopvarLog // "135"
}

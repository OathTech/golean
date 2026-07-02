package main

func stringIndexPanicEvalOrder() (result int) {
	s := "abc"
	i := 2
	defer func() {
		if recover() != nil {
			result = i
		}
	}()
	i = 4
	_ = s[i]
	return -1
}

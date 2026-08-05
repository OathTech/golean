package main

var deferRecoverTrace int

func init() {
	defer func() {
		if r := recover(); r != nil {
			deferRecoverTrace = deferRecoverTrace*10 + 2
		}
	}()
	deferRecoverTrace = deferRecoverTrace*10 + 1
	panic("init panic")
}

func init() {
	deferRecoverTrace = deferRecoverTrace*10 + 3
}

func initDeferRecover() int {
	return deferRecoverTrace
}

func main() {
	initDeferRecover()
}

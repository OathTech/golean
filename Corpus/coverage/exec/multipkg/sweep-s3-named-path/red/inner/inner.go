package inner

type T struct{ Tag int }

func (T) Name() string { return "red" }

func Make(n int) T { return T{Tag: n} }

type L int

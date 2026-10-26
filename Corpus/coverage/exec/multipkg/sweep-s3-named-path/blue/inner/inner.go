package inner

type T struct{ Tag int }

func (T) Name() string { return "blue" }

func Make(n int) T { return T{Tag: n} }

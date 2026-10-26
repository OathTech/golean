package inner

type T struct{ Tag int }

func (T) Name() string { return "red" }
func (T) get() int     { return 1 }

// Private: a NAMED interface with an unexported method; embedding it in an anonymous
// interface literal elsewhere flattens to red/inner.get — the same type as this package's
// own `interface{ get() int }`.
type Private interface{ get() int }

func FnGet() func(interface{ get() int }) { return func(interface{ get() int }) {} }

// FnErr: a func over the UNIVERSE error type.
func FnErr() func(error) { return func(error) {} }

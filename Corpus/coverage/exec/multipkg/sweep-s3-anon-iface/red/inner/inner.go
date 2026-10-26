package inner

type T struct{}

func (T) get() int { return 1 }
func (T) M()       {}

// FnGet: a func type whose parameter is THIS package's `interface{ get() int }` — its unexported
// method name belongs to red/inner, so main's spelling of the same literal is another type.
func FnGet() func(interface{ get() int }) { return func(interface{ get() int }) {} }

// FnM: the exported-method literal — identical to main's spelling of it.
func FnM() func(interface{ M() }) { return func(interface{ M() }) {} }

func SliceGet() any { return []interface{ get() int }{} }
func SliceM() any   { return []interface{ M() }{} }

func IsGet(x any) bool { _, ok := x.(interface{ get() int }); return ok }

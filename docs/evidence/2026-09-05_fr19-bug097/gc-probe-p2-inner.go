package inner

type T int

func (t T) Get() T   { return t }
func (t T) get() int { return 0 }

type Q struct{ Tag int }

func Make(v int) interface{ Get() T }       { return T(v) }
func Is(x any) bool                          { _, ok := x.(interface{ Get() T }); return ok }
func Assert(x any)                           { _ = x.(interface{ Get() T }) }
func AssertUnexp(x any)                      { _ = x.(interface{ get() int; M() }) }
func AssertQ(x any)                          { _ = x.(Q) }
func Src() interface{ Get() T }              { return T(7) }

type W int

func (W) Get() T { return 0 }

func AssertGet(x any) { _ = x.(interface{ get() int }) }
func IsGet(x any) bool { _, ok := x.(interface{ get() int }); return ok }

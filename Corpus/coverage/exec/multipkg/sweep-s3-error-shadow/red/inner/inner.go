package inner

// FnErr is a func over the UNIVERSE error type; FnInt over the universe int.
func FnErr() func(error) { return func(error) {} }
func FnInt() func(int)   { return func(int) {} }

func BoxInt() any { return int(1) }

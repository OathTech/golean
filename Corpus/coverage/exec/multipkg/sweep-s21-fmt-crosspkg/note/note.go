package note

import "fmt"

type Tag int

func (t Tag) String() string { return fmt.Errorf("tag%d", int(t)).Error() }

func Make(n int) error { return fmt.Errorf("n=%d", n) }

package main

// spec#Struct_types block Struct_types-5-677bedbd: a field declaration
// may carry a string-literal tag; an empty tag string is equivalent to
// an absent tag; any string is permitted as a tag; tags are visible
// through reflection and take part in type identity "but are otherwise
// ignored". The executable pin: tagged fields (including beside a
// blank `_` field) store and read back exactly like untagged ones —
// the tags change nothing about ordinary field access.
// Adaptation: the spec shows anonymous struct types; wrapped here as
// values of those exact anonymous types.

func structTagsIgnored() (float64, string, uint64) {
	v := struct {
		x, y float64 ""  // an empty tag string is like an absent tag
		name string  "any string is permitted as a tag"
		_    [4]byte "ceci n'est pas un champ de structure"
	}{x: 1.5, y: 2.5, name: "tagged"}
	ts := struct {
		microsec  uint64 `protobuf:"1"`
		serverIP6 uint64 `protobuf:"2"`
	}{microsec: 3, serverIP6: 4}
	return v.x + v.y, v.name, ts.microsec*10 + ts.serverIP6
}

func main() {
	structTagsIgnored()
}

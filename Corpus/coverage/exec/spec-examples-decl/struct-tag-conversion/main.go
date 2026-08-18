package main

// spec#Conversions block Conversions-5-b1bcceec: struct conversions IGNORE
// struct tags — *Person and the tagged anonymous struct pointer type are
// convertible because the underlying struct types are identical modulo tags
// (recursively, including the nested Address struct). person is the
// conversion of the nil data pointer (== nil); a second conversion of a
// non-nil tagged value carries the field data across.

type Person struct {
	Name    string
	Address *struct {
		Street string
		City   string
	}
}

var data *struct {
	Name    string `json:"name"`
	Address *struct {
		Street string `json:"street"`
		City   string `json:"city"`
	} `json:"address"`
}

var person = (*Person)(data) // ignoring tags, the underlying types are identical

func structTagConversion() string {
	if person != nil {
		return "person-not-nil"
	}
	data2 := &struct {
		Name    string `json:"name"`
		Address *struct {
			Street string `json:"street"`
			City   string `json:"city"`
		} `json:"address"`
	}{Name: "spec"}
	p2 := (*Person)(data2)
	return p2.Name // "spec"
}

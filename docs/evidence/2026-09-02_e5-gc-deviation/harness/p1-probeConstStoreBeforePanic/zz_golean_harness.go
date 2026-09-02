package main

import (
	_golean_json "encoding/json"
	_golean_fmt "fmt"
	_golean_math "math"
	_golean_os "os"
	_golean_reflect "reflect"
)

// _goleanObservationValue takes a POINTER to the observed result so the
// result's static type survives: reflect.ValueOf(x) on an interface-typed
// x reports the DYNAMIC value's kind, never reflect.Interface.
func _goleanObservationValue(ptr any) (any, error) {
	return _goleanReflectValue(_golean_reflect.ValueOf(ptr).Elem())
}

func _goleanReflectValue(value _golean_reflect.Value) (any, error) {
	if !value.IsValid() {
		return map[string]any{"tag": "nil"}, nil
	}
	switch value.Kind() {
	case _golean_reflect.Bool:
		return map[string]any{"tag": "bool", "value": value.Bool()}, nil
	// Kind-carrying integer observation (grossmith hunt F15): the reflect
	// KIND (width + signedness; "int8", "uint64", ...) rides beside the
	// value, symmetrically with the machine encoder's IntKind — a
	// kind-defaulting machine bug landing on the right numeric value was
	// invisible to the value-only shape. The defined-type name is NOT
	// emitted (the machine value carries an IntKind only; defined-type
	// identity over ints is observable only through interface boxes, on
	// both sides alike). Uintptr FAILS CLOSED below: the frontend maps
	// uintptr to uint64 (NativeToIR intKindOfName), so the machine side
	// can never answer "uintptr" and the observation could never compare
	// equal — refuse loudly rather than alias the kind away (the exact
	// F15 defect class).
	case _golean_reflect.Int, _golean_reflect.Int8, _golean_reflect.Int16, _golean_reflect.Int32, _golean_reflect.Int64:
		return map[string]any{"tag": "int", "kind": value.Kind().String(), "value": value.Int()}, nil
	case _golean_reflect.Uint, _golean_reflect.Uint8, _golean_reflect.Uint16, _golean_reflect.Uint32, _golean_reflect.Uint64:
		return map[string]any{"tag": "int", "kind": value.Kind().String(), "value": value.Uint()}, nil
	case _golean_reflect.Uintptr:
		return nil, _golean_fmt.Errorf("unsupported Go observation kind uintptr (the frontend maps uintptr to uint64; a kind-visible channel must not alias them)")
	case _golean_reflect.Float64:
		// BIT-pattern observation (floats design note S5/S7): bit-exact
		// modulo NaN canonicalization — NaN payload/sign are platform- and
		// path-dependent and unobservable in the language proper, so both
		// encoders canonicalize; signed zero stays exact. Revisit if
		// math.Float64bits ever enters the supported surface.
		f := value.Float()
		bits := _golean_math.Float64bits(f)
		if f != f {
			bits = 0x7FF8000000000000
		}
		return map[string]any{"tag": "float", "kind": "float64", "bits": bits}, nil
	case _golean_reflect.Float32:
		f := float32(value.Float())
		bits := _golean_math.Float32bits(f)
		if f != f {
			bits = 0x7FC00000
		}
		return map[string]any{"tag": "float", "kind": "float32", "bits": bits}, nil
	case _golean_reflect.String:
		bytes := []int{}
		for _, b := range []byte(value.String()) {
			bytes = append(bytes, int(b))
		}
		return map[string]any{"tag": "string", "bytes": bytes}, nil
	case _golean_reflect.Array:
		values := []any{}
		for i := 0; i < value.Len(); i++ {
			elem, err := _goleanReflectValue(value.Index(i))
			if err != nil {
				return nil, err
			}
			values = append(values, elem)
		}
		return map[string]any{"tag": "array", "values": values}, nil
	case _golean_reflect.Interface:
		// A BOXED value: Go's own model is (dynamic type, value), and the
		// machine reports exactly that. A nil interface is the nil
		// observation (no dynamic type at all).
		if value.IsNil() {
			return map[string]any{"tag": "nil"}, nil
		}
		inner := value.Elem()
		name := inner.Type().Name()
		if name == "" {
			// An UNNAMED dynamic type (*T, []T, map[K]V, func(...)):
			// reflect.Type.Name() is empty, and the observation channel's
			// stated naming contract IS reflect.Type.Name(). Fail closed
			// rather than invent a spelling the machine might or might not
			// agree with.
			return nil, _golean_fmt.Errorf("unsupported Go observation: interface holding unnamed dynamic type %s", inner.Type())
		}
		innerValue, err := _goleanReflectValue(inner)
		if err != nil {
			return nil, err
		}
		return map[string]any{"tag": "interface", "dynamic": name, "value": innerValue}, nil
	case _golean_reflect.Struct:
		fields := []any{}
		typ := value.Type()
		for i := 0; i < value.NumField(); i++ {
			fieldValue, err := _goleanReflectValue(value.Field(i))
			if err != nil {
				return nil, err
			}
			fields = append(fields, map[string]any{"name": typ.Field(i).Name, "value": fieldValue})
		}
		return map[string]any{"tag": "struct", "typeName": typ.Name(), "fields": fields}, nil
	default:
		return nil, _golean_fmt.Errorf("unsupported Go observation kind %s", value.Kind())
	}
}

func _goleanPrintOk(values []any) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": "ok", "values": values}); err != nil {
		panic(err)
	}
}

func _goleanPrintError(message string) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": "error", "message": message}); err != nil {
		panic(err)
	}
}

func main() {
	_golean_r0 := probeConstStoreBeforePanic()
	_goleanValues := []any{}
	{
		_goleanValue, _goleanErr := _goleanObservationValue(&_golean_r0)
		if _goleanErr != nil {
			_goleanPrintError(_goleanErr.Error())
			return
		}
		_goleanValues = append(_goleanValues, _goleanValue)
	}
	_goleanPrintOk(_goleanValues)
}

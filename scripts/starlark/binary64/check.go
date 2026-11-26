// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"math"
	"math/big"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func call(name string, input starlark.Value) (starlark.Value, error) {
	return starlark.Call(&starlark.Thread{Name: "binary64"}, starlark.Universe[name], starlark.Tuple{input}, nil)
}

func fromBits(bits uint64) starlark.Float { return starlark.Float(math.Float64frombits(bits)) }

func checkUnary() {
	for _, tc := range []struct {
		name      string
		bits, abs uint64
		truth     starlark.Bool
	}{
		{"positive zero", 0, 0, false},
		{"negative zero", 0x8000000000000000, 0, false},
		{"negative subnormal", 0x8000000000000001, 1, true},
		{"negative finite", 0xbff4000000000000, 0x3ff4000000000000, true},
		{"negative max finite", 0xffefffffffffffff, 0x7fefffffffffffff, true},
		{"positive infinity", 0x7ff0000000000000, 0x7ff0000000000000, true},
		{"negative infinity", 0xfff0000000000000, 0x7ff0000000000000, true},
		{"positive quiet NaN", 0x7ff8000000000021, 0x7ff8000000000021, true},
		{"negative signaling NaN", 0xfff0000000000001, 0x7ff0000000000001, true},
	} {
		x := fromBits(tc.bits)
		result, err := call("abs", x)
		abs, ok := result.(starlark.Float)
		require(err == nil && ok && math.Float64bits(float64(abs)) == tc.abs,
			fmt.Sprintf("%s: want abs bits %x, got %x (%v)", tc.name, tc.abs, math.Float64bits(float64(abs)), err))
		truth, err := call("bool", x)
		require(err == nil && truth == tc.truth, fmt.Sprintf("%s: truth %v (%v)", tc.name, truth, err))
		tag, err := call("type", x)
		require(err == nil && tag == starlark.String("float"), fmt.Sprintf("%s: type %v (%v)", tc.name, tag, err))
	}
	fmt.Println("PASS raw binary64 abs, truth and type, including signed zeros, infinities and NaN payloads")
}

func checkEqualityAndKeys() {
	for _, pair := range [][2]starlark.Value{
		{fromBits(0x8000000000000000), fromBits(0)},
		{fromBits(0xfff8000000000021), fromBits(0x7ff0000000000001)},
		{starlark.Float(1.0), starlark.MakeInt(1)},
	} {
		x, y := pair[0], pair[1]
		equal, err := starlark.Equal(x, y)
		require(err == nil && equal, fmt.Sprintf("%v == %v failed (%v)", x, y, err))
		hx, ex := x.Hash()
		hy, ey := y.Hash()
		require(ex == nil && ey == nil && hx == hy, fmt.Sprintf("inconsistent hash for %v, %v", x, y))

		for _, keys := range [][2]starlark.Value{{x, y}, {starlark.Tuple{x}, starlark.Tuple{y}}} {
			d := starlark.NewDict(1)
			require(d.SetKey(keys[0], starlark.True) == nil, "Go did not accept a float key")
			v, found, err := d.Get(keys[1])
			require(err == nil && found && v == starlark.True, fmt.Sprintf("no matching key for %v", keys[1]))
		}
	}
	fmt.Println("PASS Go equality and hash controls for signed zeros, NaNs, mixed numbers and tuple keys")
}

func checkDictionaryLookup(dict *starlark.Dict, key starlark.Value, want string) {
	got, found, err := dict.Get(key)
	require(err == nil && found && got == starlark.String(want),
		fmt.Sprintf("key %v: want %q, got %v, present %v (%v)", key, want, got, found, err))
}

func checkOriginalScalarKey(got, want starlark.Value) {
	require(got.Type() == want.Type(), fmt.Sprintf("key type changed from %s to %s", want.Type(), got.Type()))
	if floating, ok := want.(starlark.Float); ok {
		require(math.Float64bits(float64(got.(starlark.Float))) == math.Float64bits(float64(floating)),
			fmt.Sprintf("float key bits changed for %v", want))
	} else {
		equal, err := starlark.Equal(got, want)
		require(err == nil && equal, fmt.Sprintf("key changed from %v to %v (%v)", want, got, err))
	}
}

func checkNumericDictionaryUpdates() {
	negZero := fromBits(0x8000000000000000)
	firstNaN, secondNaN := fromBits(0xfff0000000000001), fromBits(0x7ff8000000000021)
	posInf, negInf := fromBits(0x7ff0000000000000), fromBits(0xfff0000000000000)
	boundary, adjacentInt := fromBits(0x4340000000000000), starlark.MakeInt64((1<<53)+1)
	zero, one := starlark.MakeInt(0), starlark.MakeInt(1)
	fraction := starlark.Float(1.5)
	dict := starlark.NewDict(0)
	for _, tc := range []struct {
		key   starlark.Value
		value string
	}{
		{negZero, "first zero"}, {starlark.False, "bool"}, {firstNaN, "first NaN"}, {posInf, "+inf"},
		{zero, "zero"}, {secondNaN, "nan"}, {negInf, "-inf"},
		{boundary, "rounded boundary"}, {adjacentInt, "exact integer"}, {one, "first one"},
		{starlark.Float(1), "one"}, {fraction, "fraction"},
	} {
		err := dict.SetKey(tc.key, starlark.String(tc.value))
		require(err == nil, fmt.Sprint(err))
	}
	for _, tc := range []struct {
		key  starlark.Value
		want string
	}{
		{fromBits(0), "zero"}, {negZero, "zero"}, {starlark.False, "bool"},
		{firstNaN, "nan"}, {secondNaN, "nan"}, {posInf, "+inf"}, {negInf, "-inf"},
		{starlark.MakeInt64(1 << 53), "rounded boundary"}, {adjacentInt, "exact integer"}, {one, "one"},
		{fraction, "fraction"},
	} {
		checkDictionaryLookup(dict, tc.key, tc.want)
	}
	iter := dict.Iterate()
	defer iter.Done()
	var got starlark.Value
	for _, want := range []starlark.Value{negZero, starlark.False, firstNaN, posInf, negInf, boundary, adjacentInt, one, fraction} {
		require(iter.Next(&got), "dictionary lost an original key")
		checkOriginalScalarKey(got, want)
	}
	require(!iter.Next(&got), "numeric replacement added another key")

	outer := starlark.Tuple{starlark.String("pair"), starlark.Tuple{negZero, firstNaN}}
	alternate := starlark.Tuple{starlark.String("pair"), starlark.Tuple{zero, secondNaN}}
	nested := starlark.NewDict(0)
	require(nested.SetKey(outer, starlark.String("first")) == nil, "nested tuple insertion failed")
	require(nested.SetKey(alternate, starlark.String("updated")) == nil, "nested tuple update failed")
	checkDictionaryLookup(nested, alternate, "updated")
	keys := nested.Keys()
	require(len(keys) == 1, "equivalent nested tuples produced two keys")
	inner := keys[0].(starlark.Tuple)[1].(starlark.Tuple)
	checkOriginalScalarKey(inner[0], negZero)
	checkOriginalScalarKey(inner[1], firstNaN)

	_, err := starlark.Eval(&starlark.Thread{}, "numeric-keys.star", `{original: "first", duplicate: "second"}`,
		starlark.StringDict{"original": negZero, "duplicate": zero})
	require(err != nil && strings.Contains(err.Error(), "duplicate key"), fmt.Sprintf("want duplicate key, got %v", err))

	var deepOriginal, deepAlternate starlark.Value = negZero, zero
	for range starlark.CompareLimit {
		deepOriginal, deepAlternate = starlark.Tuple{deepOriginal}, starlark.Tuple{deepAlternate}
	}
	deep := starlark.NewDict(0)
	require(deep.SetKey(deepOriginal, starlark.True) == nil, "deep tuple insertion failed")
	_, _, err = deep.Get(deepAlternate)
	require(err != nil && strings.Contains(err.Error(), "comparison exceeded maximum recursion depth"),
		fmt.Sprintf("want Go's tuple comparison depth error, got %v", err))

	fmt.Println("PASS numeric dictionary updates, nested tuple keys, duplicate display and Go's depth limit")
}

func checkOrder(left, right starlark.Value, order int) {
	for _, tc := range []struct {
		op   syntax.Token
		want bool
	}{
		{syntax.EQL, order == 0}, {syntax.NEQ, order != 0},
		{syntax.LT, order < 0}, {syntax.LE, order <= 0},
		{syntax.GT, order > 0}, {syntax.GE, order >= 0},
	} {
		got, err := starlark.Compare(tc.op, left, right)
		require(err == nil && got == tc.want,
			fmt.Sprintf("%v %s %v: want %v, got %v (%v)", left, tc.op, right, tc.want, got, err))
	}
}

func checkScalarComparison() {
	negZero, posZero := fromBits(0x8000000000000000), fromBits(0)
	posNaN, negNaN := fromBits(0x7ff8000000000021), fromBits(0xfff0000000000001)
	posInf, negInf := starlark.Float(math.Inf(1)), starlark.Float(math.Inf(-1))
	boundary := fromBits(0x4340000000000000)
	huge := new(big.Int).Lsh(big.NewInt(1), 1100)
	for _, tc := range []struct {
		left, right starlark.Value
		order       int
	}{
		{negZero, posZero, 0}, {negZero, starlark.MakeInt(0), 0},
		{fromBits(0x8000000000000001), negZero, -1}, {fromBits(1), starlark.MakeInt(0), 1},
		{fromBits(0x000fffffffffffff), fromBits(0x0010000000000000), -1},
		{starlark.MakeInt(1), starlark.Float(1.5), -1}, {starlark.MakeInt(2), starlark.Float(1.5), 1},
		{starlark.Float(-1.5), starlark.MakeInt(-1), -1},
		{starlark.MakeInt64(1 << 53), boundary, 0}, {starlark.MakeInt64((1 << 53) + 1), boundary, 1},
		{starlark.MakeInt64((1 << 53) + 1), fromBits(0x4340000000000001), -1},
		{starlark.MakeInt64(-(1 << 53) - 1), fromBits(0xc340000000000000), -1},
		{starlark.Float(math.MaxFloat64), starlark.MakeBigInt(new(big.Int).Lsh(big.NewInt(1), 1024)), -1},
		{starlark.MakeBigInt(huge), posInf, -1}, {starlark.MakeBigInt(new(big.Int).Neg(huge)), negInf, 1},
		{negInf, posInf, -1}, {posInf, posInf, 0},
		{posNaN, negNaN, 0}, {posNaN, posInf, 1}, {starlark.MakeBigInt(huge), negNaN, -1},
		{starlark.False, starlark.True, -1},
	} {
		checkOrder(tc.left, tc.right, tc.order)
		checkOrder(tc.right, tc.left, -tc.order)
	}
	for _, pair := range [][2]starlark.Value{
		{starlark.True, starlark.MakeInt(1)}, {starlark.False, posZero},
		{starlark.Float(1), starlark.True}, {posNaN, starlark.None},
	} {
		left, right := pair[0], pair[1]
		equal, eqErr := starlark.Compare(syntax.EQL, left, right)
		unequal, neErr := starlark.Compare(syntax.NEQ, right, left)
		_, ltErr := starlark.Compare(syntax.LT, left, right)
		_, geErr := starlark.Compare(syntax.GE, right, left)
		require(eqErr == nil && !equal && neErr == nil && unequal && ltErr != nil && geErr != nil,
			fmt.Sprintf("unexpected comparison across types %s and %s", left.Type(), right.Type()))
	}
	fmt.Println("PASS all six scalar comparisons, including exact mixed order and Boolean distinctions")
}

func checkConversionOverflow() {
	huge := starlark.MakeBigInt(new(big.Int).Lsh(big.NewInt(1), 1100))
	for _, input := range []starlark.Value{huge, starlark.String("1e9999")} {
		_, err := call("float", input)
		require(err != nil && strings.Contains(err.Error(), "too large"), fmt.Sprintf("want conversion overflow, got %v", err))
	}
	value, err := call("float", starlark.String("-inf"))
	require(err == nil && value == starlark.Float(math.Inf(-1)), fmt.Sprintf("explicit infinity %v (%v)", value, err))
	product, err := starlark.Binary(syntax.STAR, starlark.Float(math.MaxFloat64), starlark.Float(2))
	require(err == nil && product == starlark.Float(math.Inf(1)), fmt.Sprintf("arithmetic overflow %v (%v)", product, err))
	fmt.Println("PASS Go rejects conversion overflow and admits explicit or arithmetic infinity")
}

func main() {
	checkUnary()
	checkEqualityAndKeys()
	checkNumericDictionaryUpdates()
	checkScalarComparison()
	checkConversionOverflow()
}

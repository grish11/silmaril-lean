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

type comparisonCase struct {
	name        string
	op          syntax.Token
	left, right starlark.Value
	want        bool
	depthError  bool
}

func checkComparisonCases(cases []comparisonCase) {
	for _, tc := range cases {
		var got bool
		var err error
		if tc.op == syntax.IN || tc.op == syntax.NOT_IN {
			var value starlark.Value
			value, err = starlark.Binary(tc.op, tc.left, tc.right)
			if value != nil {
				got = value == starlark.True
			}
		} else {
			got, err = starlark.Compare(tc.op, tc.left, tc.right)
		}
		if tc.depthError {
			require(err != nil && strings.Contains(err.Error(), "comparison exceeded maximum recursion depth"),
				fmt.Sprintf("%s: want depth error, got %v", tc.name, err))
		} else {
			require(err == nil && got == tc.want, fmt.Sprintf("%s: got %v (%v)", tc.name, got, err))
		}
	}
}

func checkTupleComparison() {
	boundary := starlark.MakeInt64(1 << 53)
	zero, one := starlark.MakeInt(0), starlark.MakeInt(1)
	negZero := fromBits(0x8000000000000000)
	left := starlark.Tuple{starlark.String("tag"), starlark.Tuple{boundary, zero, fromBits(0x7ff8000000000021)}}
	right := starlark.Tuple{starlark.String("tag"), starlark.Tuple{fromBits(0x4340000000000000), negZero,
		fromBits(0xfff0000000000001)}}
	larger := starlark.Tuple{starlark.String("tag"), starlark.Tuple{starlark.MakeInt64((1 << 53) + 1), zero,
		fromBits(0x7ff8000000000021)}}
	dict := starlark.NewDict(0)
	require(dict.SetKey(left, starlark.String("same")) == nil, "tuple key insertion failed")
	checkDictionaryLookup(dict, right, "same")

	wrap := func(levels int, value starlark.Value) starlark.Value {
		for range levels {
			value = starlark.Tuple{value}
		}
		return value
	}
	require(starlark.CompareLimit == 10, "pinned default comparison limit changed")
	nine, nineFloat := wrap(9, zero), wrap(9, negZero)
	ten, tenFloat := starlark.Tuple{nine}, starlark.Tuple{nineFloat}
	list := starlark.NewList([]starlark.Value{one})
	checkComparisonCases([]comparisonCase{
		{"nested numeric aliases", syntax.EQL, left, right, true, false},
		{"int around 2^53", syntax.NEQ, left, larger, true, false},
		{"mixed numeric membership", syntax.IN, left, starlark.Tuple{larger, right}, true, false},
		{"bool and int", syntax.NEQ, starlark.Tuple{starlark.False}, starlark.Tuple{zero}, true, false},
		{"membership exhausts", syntax.NOT_IN, one, starlark.Tuple{zero, starlark.False}, true, false},
		{"equal at depth limit", syntax.EQL, nine, nineFloat, true, false},
		{"field exceeds limit", syntax.EQL, ten, tenFloat, false, true},
		{"negation preserves error", syntax.NEQ, ten, tenFloat, false, true},
		{"length before depth", syntax.EQL, starlark.Tuple{ten}, starlark.Tuple{tenFloat, zero}, false, false},
		{"early field mismatch", syntax.EQL, starlark.Tuple{zero, ten}, starlark.Tuple{one, tenFloat}, false, false},
		{"fresh membership limit", syntax.IN, nineFloat, ten, true, false},
		{"first hit before deep candidate", syntax.NOT_IN, nineFloat, starlark.Tuple{nine, ten}, false, false},
		{"reached membership depth", syntax.IN, tenFloat, starlark.Tuple{ten}, false, true},
		{"negated membership preserves error", syntax.NOT_IN, tenFloat, starlark.Tuple{ten}, false, true},
		{"lists within tuples", syntax.EQL, starlark.Tuple{list}, starlark.Tuple{list}, true, false},
	})
	fmt.Println("PASS tuple equality, membership, key coherence, short-circuit and Go comparison depth controls")
}

func checkListComparison() {
	list := func(fields ...starlark.Value) *starlark.List { return starlark.NewList(fields) }
	zero, one, two := starlark.MakeInt(0), starlark.MakeInt(1), starlark.MakeInt(2)
	negZero := fromBits(0x8000000000000000)
	ints := list(starlark.MakeInt64(1<<53), zero, fromBits(0x7ff8000000000021))
	floats := list(fromBits(0x4340000000000000), negZero, fromBits(0xfff0000000000001))
	left, right := list(starlark.Tuple{ints}), list(starlark.Tuple{floats})

	cycle, different, separate := list(zero), list(one), list(zero)
	for _, x := range []*starlark.List{cycle, different, separate} {
		require(x.Append(x) == nil, "self-cycle construction failed")
	}
	mixedCycle := list()
	require(mixedCycle.Append(starlark.Tuple{mixedCycle}) == nil, "mixed cycle construction failed")

	wrap := func(leaf starlark.Value) starlark.Value {
		for i := range 9 {
			if i%2 == 0 {
				leaf = list(leaf)
			} else {
				leaf = starlark.Tuple{leaf}
			}
		}
		return leaf
	}
	nine, nineFloat := wrap(zero), wrap(negZero)
	ten, tenFloat := starlark.Tuple{nine}, starlark.Tuple{nineFloat}
	checkComparisonCases([]comparisonCase{
		{"numeric aliases through list and tuple", syntax.EQL, left, right, true, false},
		{"mixed nested list membership", syntax.IN, left, list(list(), right), true, false},
		{"list and tuple have different types", syntax.NEQ, left, starlark.Tuple{starlark.Tuple{ints}}, true, false},
		{"bool and int list leaves", syntax.NEQ, list(starlark.False), list(zero), true, false},
		{"Go admits dictionary leaves", syntax.EQL, list(starlark.NewDict(0)), list(starlark.NewDict(0)), true, false},
		{"NaN compares equal in an aliased list", syntax.EQL, ints, ints, true, false},
		{"length mismatch skips a cycle", syntax.EQL, cycle, list(cycle), false, false},
		{"first field skips a cycle", syntax.EQL, cycle, different, false, false},
		{"separate cycles exhaust the budget", syntax.EQL, cycle, separate, false, true},
		{"self-cycle has no identity shortcut", syntax.EQL, cycle, cycle, false, true},
		{"mixed self-cycle negation preserves failure", syntax.NEQ, mixedCycle, mixedCycle, false, true},
		{"membership reaches a cycle", syntax.IN, cycle, list(cycle), false, true},
		{"list membership exhaustion", syntax.NOT_IN, one, list(zero, starlark.False), true, false},
		{"mixed nesting at the limit", syntax.EQL, nine, nineFloat, true, false},
		{"mixed nesting exceeds the limit", syntax.EQL, ten, tenFloat, false, true},
		{"first mismatch skips depth exhaustion", syntax.EQL, list(zero, ten), list(one, tenFloat), false, false},
		{"list membership restarts the budget", syntax.IN, nineFloat, list(nine), true, false},
		{"negated list membership preserves depth error", syntax.NOT_IN, tenFloat, list(ten), false, true},
	})

	actual, expected := list(one), list(one, two)
	checkComparisonCases([]comparisonCase{{"before mutation", syntax.EQL, actual, expected, false, false}})
	value, err := starlark.Eval(&starlark.Thread{}, "list-comparison.star",
		`actual == (actual.append(2), expected)[1]`, starlark.StringDict{"actual": actual, "expected": expected})
	require(err == nil && value == starlark.True && actual.Len() == 2 && actual.Index(1) == two,
		fmt.Sprintf("comparison after right operand mutation: %v (%v)", value, err))
	fmt.Println("PASS list equality and membership, mixed nesting, live mutation, and cycle depth including aliases")
}

func checkDictionaryComparison() {
	dict := func(fields ...starlark.Value) *starlark.Dict {
		x := starlark.NewDict(len(fields) / 2)
		for i := 0; i < len(fields); i += 2 {
			require(x.SetKey(fields[i], fields[i+1]) == nil, "dictionary fixture insertion failed")
		}
		return x
	}
	zero, one, two, three := starlark.MakeInt(0), starlark.MakeInt(1), starlark.MakeInt(2), starlark.MakeInt(3)
	negZero := fromBits(0x8000000000000000)
	boundary, floatBoundary := starlark.MakeInt64(1<<53), fromBits(0x4340000000000000)
	n, guard, cycle, missing, self := starlark.String("n"), starlark.String("guard"), starlark.String("cycle"),
		starlark.String("missing"), starlark.String("self")
	leftValue := starlark.Tuple{starlark.NewList([]starlark.Value{dict(n, zero), three})}
	rightValue := starlark.Tuple{starlark.NewList([]starlark.Value{dict(n, negZero), starlark.Float(3)})}
	left, right := dict(boundary, leftValue, starlark.False, one), dict(starlark.False, one, floatBoundary, rightValue)
	checkComparisonCases([]comparisonCase{{"numeric keys across insertion orders", syntax.EQL, left, right, true, false}})
	require(left.SetKey(floatBoundary, starlark.MakeInt(7)) == nil, "numeric replacement failed")
	checkComparisonCases([]comparisonCase{{"compare after replacement", syntax.NEQ, left, right, true, false}})

	cycleLeft, cycleRight := dict(), dict()
	require(cycleLeft.SetKey(self, cycleLeft) == nil && cycleRight.SetKey(self, cycleRight) == nil,
		"dictionary cycle construction failed")
	guardFirst, cycleFirst := dict(guard, zero, cycle, cycleLeft), dict(cycle, cycleRight, guard, one)
	missingFirst := dict(missing, zero, cycle, cycleLeft)
	wrap := func(depth int, leaf starlark.Value) starlark.Value {
		for range depth {
			leaf = dict(n, leaf)
		}
		return leaf
	}
	nine, nineFloat := wrap(9, zero), wrap(9, negZero)
	checkComparisonCases([]comparisonCase{
		{"size mismatch skips value", syntax.EQL, cycleLeft, dict(), false, false},
		{"self-cycle has no identity shortcut", syntax.EQL, cycleLeft, cycleLeft, false, true},
		{"early mismatch masks later cycle", syntax.EQL, guardFirst, cycleFirst, false, false},
		{"left insertion order reaches cycle first", syntax.EQL, cycleFirst, guardFirst, false, true},
		{"early key miss masks cycle", syntax.EQL, missingFirst, cycleFirst, false, false},
		{"cycle before a later missing key", syntax.NEQ, cycleFirst, missingFirst, false, true},
		{"dict nesting at limit", syntax.EQL, nine, nineFloat, true, false},
		{"dict nesting exceeds limit", syntax.EQL, dict(n, nine), dict(n, nineFloat), false, true},
	})

	var key, floatKey starlark.Value = zero, negZero
	for range starlark.CompareLimit - 1 {
		key, floatKey = starlark.Tuple{key}, starlark.Tuple{floatKey}
	}
	checkComparisonCases([]comparisonCase{
		{"key probe starts at full default depth", syntax.IN, key, dict(floatKey, one), true, false},
	})
	key, floatKey = starlark.Tuple{key}, starlark.Tuple{floatKey}
	deepLeft, deepRight := dict(key, one), dict(floatKey, one)
	_, found, err := deepRight.Get(key)
	require(!found && err != nil && strings.Contains(err.Error(), "comparison exceeded maximum recursion depth"),
		fmt.Sprintf("want key lookup depth error, got %v", err))
	checkComparisonCases([]comparisonCase{
		{"Go treats deep-key lookup error as a miss", syntax.EQL, deepLeft, deepRight, false, false},
		{"deep-key membership swallows lookup error", syntax.IN, key, deepRight, false, false},
		{"negated membership complements the miss", syntax.NOT_IN, key, deepRight, true, false},
	})
	var collisionKey starlark.Value = starlark.MakeInt64(1 << 32)
	for range starlark.CompareLimit {
		collisionKey = starlark.Tuple{collisionKey}
	}
	keyHash, keyHashErr := key.Hash()
	collisionHash, collisionHashErr := collisionKey.Hash()
	require(keyHashErr == nil && collisionHashErr == nil && keyHash == collisionHash,
		"unequal numeric tuple keys did not collide")
	colliding := dict(collisionKey, one)
	_, found, err = colliding.Get(key)
	require(!found && err != nil && strings.Contains(err.Error(), "comparison exceeded maximum recursion depth"),
		fmt.Sprintf("want depth error probing an unequal colliding key, got %v", err))
	checkComparisonCases([]comparisonCase{
		{"same hash can reach unequal deep key", syntax.IN, key, colliding, false, false},
	})
	// SetKey would itself compare the deep key if the entry already existed.
	deepLeft, deepRight = dict(key, cycleLeft), dict(floatKey, cycleRight)
	checkComparisonCases([]comparisonCase{
		{"Go's key error masks the cyclic value", syntax.EQL, deepLeft, deepRight, false, false},
		{"the same error hides the cyclic entry from membership", syntax.NOT_IN, key, deepRight, true, false},
	})

	events := starlark.NewList([]starlark.Value{one})
	actual, expected := dict(n, events), dict(n, starlark.NewList([]starlark.Value{one, two}))
	checkComparisonCases([]comparisonCase{{"before operand mutation", syntax.EQL, actual, expected, false, false}})
	value, err := starlark.Eval(&starlark.Thread{}, "dict-comparison.star",
		`actual == (actual["n"].append(2), expected)[1]`, starlark.StringDict{"actual": actual, "expected": expected})
	require(err == nil && value == starlark.True && events.Len() == 2 && events.Index(1) == two,
		fmt.Sprintf("dictionary comparison after operand mutation: %v (%v)", value, err))
	fmt.Println("PASS dictionary equality, numeric key correspondence, live values, left-order cycle masking, and Go deep-key misses")
}

func checkDictionaryMembership() {
	zero, one := starlark.MakeInt(0), starlark.MakeInt(1)
	negZero := fromBits(0x8000000000000000)
	flagOnly, table := starlark.NewDict(0), starlark.NewDict(0)
	require(flagOnly.SetKey(starlark.False, one) == nil, "Boolean key insertion failed")
	for _, key := range []starlark.Value{starlark.False, zero, starlark.MakeInt64(1 << 53),
		starlark.Tuple{zero, fromBits(0x7ff8000000000021)}} {
		require(table.SetKey(key, table) == nil, "cyclic entry insertion failed")
	}
	checkComparisonCases([]comparisonCase{
		{"Boolean key differs from zero", syntax.IN, zero, flagOnly, false, false},
		{"Boolean key is present", syntax.IN, starlark.False, table, true, false},
		{"signed zero alias", syntax.IN, negZero, table, true, false},
		{"int-float alias at 2^53", syntax.IN, fromBits(0x4340000000000000), table, true, false},
		{"adjacent int remains absent", syntax.NOT_IN, starlark.MakeInt64((1 << 53) + 1), table, true, false},
		{"tuple aliases with cyclic value", syntax.IN, starlark.Tuple{negZero, fromBits(0xfff0000000000001)}, table, true, false},
	})
	badList := starlark.NewList([]starlark.Value{one})
	badList.Freeze()
	for _, key := range []starlark.Value{badList, starlark.Tuple{badList}, table} {
		for _, target := range []*starlark.Dict{starlark.NewDict(0), table} {
			_, found, err := target.Get(key)
			require(!found && err != nil && strings.Contains(err.Error(), "unhashable"),
				fmt.Sprintf("want unhashable lookup error for %s, got %v", key.Type(), err))
			checkComparisonCases([]comparisonCase{
				{"membership discards unhashable error", syntax.IN, key, target, false, false},
				{"negated membership sees absence", syntax.NOT_IN, key, target, true, false},
			})
		}
	}
	events := starlark.NewList(nil)
	result, err := starlark.Eval(&starlark.Thread{}, "dict-membership.star",
		`(events.append(1), events)[1] not in (events.append(2), target)[1]`,
		starlark.StringDict{"events": events, "target": table})
	require(err == nil && result == starlark.True && events.Len() == 2 &&
		events.Index(0) == one && events.Index(1) == starlark.MakeInt(2),
		fmt.Sprintf("membership operand order: %v (%v)", result, err))
	fmt.Println("PASS Go dictionary membership, operand effects, numeric keys, and raw lookup error suppression")
}

func main() {
	checkUnary()
	checkEqualityAndKeys()
	checkNumericDictionaryUpdates()
	checkScalarComparison()
	checkTupleComparison()
	checkListComparison()
	checkDictionaryComparison()
	checkDictionaryMembership()
	checkConversionOverflow()
}

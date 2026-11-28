// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"math"
	"math/big"
	"slices"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func fromBits(bits uint64) starlark.Float { return starlark.Float(math.Float64frombits(bits)) }

func wrap(key starlark.Value) starlark.Value {
	for range 10 {
		key = starlark.Tuple{key}
	}
	return key
}

func checkHashes() {
	large := new(big.Int).Lsh(big.NewInt(1), 80)
	large.Neg(large.Add(large, big.NewInt(1)))
	for _, tc := range []struct {
		key  starlark.Value
		want uint32
	}{
		{starlark.None, 0x00000000}, {starlark.False, 0x00000000}, {starlark.True, 0x00000001},
		{starlark.MakeInt(-3), 0x00000000},
		{starlark.MakeInt64(-2147483649), 0x83000014}, {starlark.MakeInt64(-2147483648), 0x8240000f},
		{starlark.MakeInt64(2147483647), 0x8180000a}, {starlark.MakeInt64(2147483648), 0x8240000f},
		{starlark.MakeInt(0), 0x0240000f}, {starlark.MakeInt64(1 << 32), 0x0240000f},
		{starlark.MakeBigInt(large), 0x03000014},
		{fromBits(0x8000000000000000), 0x0240000f}, {fromBits(0x3ff8000000000000), 0x03000014},
		{fromBits(0xc00e000000000000), 0x00000000}, {fromBits(1), 0x0240000f},
		{fromBits(0x43e0000000000001), 0x0240280f}, {fromBits(0xc3e0000000000001), 0x0240280f},
		{fromBits(0x7ff0000000000000), 0x0018b071}, {fromBits(0xfff0000000000000), 0x0018b071},
		{fromBits(0x7ff8000000000021), 0x0018b071}, {fromBits(0xfff0000000000001), 0x0018b071},
		{starlark.Tuple{}, 0x00345678},
		{starlark.Tuple{starlark.False, starlark.MakeInt(3), fromBits(0xc00e000000000000),
			starlark.Tuple{starlark.MakeInt64(1 << 32), fromBits(0x7ff8000000000021)}}, 0x8ebb258c},
		{wrap(starlark.MakeInt(0)), 0xa77087e7}, {wrap(starlark.MakeInt64(1 << 32)), 0xa77087e7},
	} {
		hash, err := tc.key.Hash()
		require(err == nil && hash == tc.want, fmt.Sprintf("%v: hash %08x, want %08x (%v)", tc.key, hash, tc.want, err))
	}
	fmt.Println("PASS pinned scalar and tuple hash vectors")
}

// This host-only diagnostic records actual probe order in the pinned table.
type traceKey struct {
	id        int
	word      uint32
	visits    *[]int
	hashCalls *int
}

func (k traceKey) String() string     { return fmt.Sprint(k.id) }
func (traceKey) Type() string         { return "trace_key" }
func (traceKey) Freeze()              {}
func (traceKey) Truth() starlark.Bool { return starlark.True }
func (k traceKey) Hash() (uint32, error) {
	if k.hashCalls != nil {
		*k.hashCalls++
	}
	return k.word, nil
}
func (k traceKey) CompareSameType(op syntax.Token, y starlark.Value, depth int) (bool, error) {
	require(op == syntax.EQL && depth == starlark.CompareLimit, "unexpected key comparison")
	other := y.(traceKey)
	if k.visits != nil {
		*k.visits = append(*k.visits, other.id)
	}
	return k.id == other.id, nil
}

func checkSlots() {
	traced := starlark.NewDict(0)
	for i := range 8 {
		require(traced.SetKey(traceKey{id: i, word: 1}, starlark.MakeInt(i)) == nil, "trace insertion failed")
	}
	var visited []int
	_, found, err := traced.Get(traceKey{id: 3, word: 1, visits: &visited})
	require(err == nil && found && slices.Equal(visited, []int{7, 6, 5, 4, 3}),
		fmt.Sprintf("unexpected slot prefix %v (%v)", visited, err))
	require(traced.SetKey(traceKey{id: 3, word: 1}, starlark.MakeInt(99)) == nil, "trace replacement failed")
	visited = nil
	_, found, err = traced.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{7, 6, 5, 4, 3, 2, 1, 0}),
		fmt.Sprintf("unexpected slot order after replacement %v (%v)", visited, err))

	dict := starlark.NewDict(0)
	for i := range 8 {
		key := starlark.MakeInt64(int64(i) << 32)
		require(dict.SetKey(key, starlark.MakeInt(i)) == nil, "numeric collision insertion failed")
	}
	require(dict.SetKey(fromBits(0x8000000000000000), starlark.MakeInt(99)) == nil, "float alias replacement failed")
	for i, key := range dict.Keys() {
		integer, ok := key.(starlark.Int)
		require(ok, "replacement changed the stored key type")
		bits, fits := integer.Int64()
		require(fits && bits == int64(i)<<32, "replacement changed numeric key or iteration order")
		want := i
		if i == 0 {
			want = 99
		}
		value, found, err := dict.Get(key)
		require(err == nil && found && value == starlark.MakeInt(want), "wrong colliding key value")
	}
	require(dict.Len() == 8, "replacement at capacity grew the dictionary")
	fmt.Println("PASS single-bucket slot order, eight numeric collisions, and in-place replacement")
}

func checkGrowth() {
	traced := starlark.NewDict(0)
	var hashCalls int
	for i := range 13 {
		if i == 8 || i == 12 {
			// A hit at eight must skip the first rehash. Another hit exercises overflow.
			before := hashCalls
			replaced := 3
			if i == 12 {
				replaced = 8
			}
			require(traced.SetKey(traceKey{id: replaced, word: 1}, starlark.MakeInt(99)) == nil,
				"growth fixture replacement failed")
			require(hashCalls == before, "replacement rehashed stored keys")
		}
		require(traced.SetKey(traceKey{id: i, word: 1, hashCalls: &hashCalls}, starlark.MakeInt(i)) == nil,
			"growth fixture insertion failed")
		if i == 8 {
			require(hashCalls == 17, "ninth miss must recompute all eight stored hashes")
		}
	}
	for i, key := range traced.Keys() {
		saved := key.(traceKey)
		require(saved.id == i && saved.hashCalls == &hashCalls, "rehash or replacement changed a stored key")
	}
	var visited []int
	_, found, err := traced.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{7, 6, 5, 4, 3, 2, 1, 0, 8, 12, 11, 10, 9}),
		fmt.Sprintf("unexpected primary and overflow order %v (%v)", visited, err))

	split := starlark.NewDict(0)
	for i := range 9 {
		word := uint32(1)
		if i == 0 {
			word = 2
		}
		require(split.SetKey(traceKey{id: i, word: word}, starlark.MakeInt(i)) == nil, "split trace insertion failed")
	}
	visited = nil
	_, found, err = split.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{8, 7, 6, 5, 4, 3, 2, 1}),
		fmt.Sprintf("ninth key must fit the split primary chain, visited %v (%v)", visited, err))

	for _, splitBit := range []bool{false, true} {
		dict := starlark.NewDict(0)
		keyAt := func(i int) int64 {
			if splitBit && i == 0 {
				return 1
			}
			return int64(i) << 32
		}
		for i := range 13 {
			if i == 8 {
				aliasBits := uint64(0x8000000000000000)
				if splitBit {
					aliasBits = 0x3ff0000000000000
				}
				require(dict.SetKey(fromBits(aliasBits), starlark.MakeInt(99)) == nil, "numeric alias replacement failed")
			}
			require(dict.SetKey(starlark.MakeInt64(keyAt(i)), starlark.MakeInt(i)) == nil, "post-threshold insertion failed")
		}
		for i, key := range dict.Keys() {
			integer, ok := key.(starlark.Int)
			require(ok, "rehash changed the stored integer to its float alias")
			bits, fits := integer.Int64()
			require(fits && bits == keyAt(i), "rehash changed iteration order or key")
			want := i
			if i == 0 {
				want = 99
			}
			value, found, err := dict.Get(key)
			require(err == nil && found && value == starlark.MakeInt(want), "rehash lost a numeric key or value")
		}
		require(dict.Len() == 13, "unexpected numeric count after growth")
	}
	fmt.Println("PASS first rehash, full-hash collisions, low-bit split, overflow slots and stored keys")
}

func checkSecondRehash() {
	for _, split := range []bool{false, true} {
		traced, dict := starlark.NewDict(0), starlark.NewDict(0)
		var hashCalls int
		count := 18
		if split {
			count = 14
		}
		for i := range count {
			if i == 13 {
				var visited []int
				_, found, err := traced.Get(traceKey{id: -1, word: 3, visits: &visited})
				if split {
					require(err == nil && !found && slices.Equal(visited, []int{7, 6, 5, 4, 3, 2, 1, 8, 12, 11, 10, 9}),
						fmt.Sprintf("unexpected candidates before second split %v (%v)", visited, err))
				}
				before := hashCalls
				word, alias := uint32(3), fromBits(0x8000000000000000)
				if split {
					word, alias = 1, starlark.Float(2)
				}
				require(traced.SetKey(traceKey{id: 0, word: word}, starlark.MakeInt(99)) == nil &&
					hashCalls == before, "replacement at thirteen triggered a rehash")
				require(dict.SetKey(alias, starlark.MakeInt(99)) == nil, "replacement at thirteen failed")
			}
			word, integer := uint32(3), int64(i)<<32
			if i == 0 && split {
				word, integer = 1, 2
			}
			require(traced.SetKey(traceKey{id: i, word: word, hashCalls: &hashCalls}, starlark.MakeInt(i)) == nil,
				"second rehash trace insertion failed")
			require(dict.SetKey(starlark.MakeInt64(integer), starlark.MakeInt(i)) == nil,
				"second rehash integer insertion failed")
			if i == 13 {
				require(hashCalls == 14+8+13, "fourteenth miss must recompute the thirteen stored hashes")
			}
		}
		want := []int{7, 6, 5, 4, 3, 2, 1, 0, 8, 15, 14, 13, 12, 11, 10, 9, 16, 17}
		if split {
			want = []int{8, 7, 6, 5, 4, 3, 2, 1, 9, 13, 12, 11, 10}
		}
		var visited []int
		_, found, err := traced.Get(traceKey{id: -1, word: 3, visits: &visited})
		require(err == nil && !found && slices.Equal(visited, want),
			fmt.Sprintf("unexpected width-four probe order %v (%v)", visited, err))
		require(dict.Len() == count, "wrong numeric count after second rehash")
		for i, key := range dict.Keys() {
			integer, ok := key.(starlark.Int)
			require(ok, "second rehash changed the stored integer to its float alias")
			bits, fits := integer.Int64()
			wantKey, wantValue := int64(i)<<32, i
			if i == 0 {
				wantValue = 99
				if split {
					wantKey = 2
				}
			}
			require(fits && bits == wantKey, "second rehash changed iteration order or key")
			value, found, err := dict.Get(key)
			require(err == nil && found && value == starlark.MakeInt(wantValue),
				"second rehash lost a numeric key or value")
		}
	}
	fmt.Println("PASS second rehash, reordered collisions after splitting, and multiple overflow links")
}

func checkDepthError() {
	zero, one := starlark.MakeInt(0), starlark.MakeInt(1)
	deep, colliding := wrap(zero), wrap(starlark.MakeInt64(1<<32))
	dict := starlark.NewDict(0)
	require(dict.SetKey(colliding, one) == nil, "deep key insertion failed")
	_, found, err := dict.Get(deep)
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		fmt.Sprintf("want a reached depth error for an unequal colliding key, got %v", err))
	require(dict.SetKey(deep, one) != nil && dict.Len() == 1, "failed probe changed the dictionary")
	member, err := starlark.Binary(syntax.IN, deep, dict)
	require(err == nil && member == starlark.False, "mapping membership did not project the lookup error to a miss")

	cycle := starlark.NewDict(0)
	require(cycle.SetKey(zero, cycle) == nil, "cycle construction failed")
	left, right := starlark.NewDict(0), starlark.NewDict(0)
	require(left.SetKey(deep, cycle) == nil && right.SetKey(wrap(fromBits(0x8000000000000000)), cycle) == nil,
		"deep alias insertion failed")
	_, found, err = right.Get(deep)
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		"a deep alias must reach a raw depth error despite equal scalar leaves")
	aliasMember, err := starlark.Binary(syntax.IN, deep, right)
	require(err == nil && aliasMember == starlark.False, "deep alias membership must observe the depth failure as a miss")
	equal, err := starlark.Compare(syntax.EQL, left, right)
	require(err == nil && !equal, fmt.Sprintf("lookup error should mask the cyclic value, got %v (%v)", equal, err))
	_, err = starlark.Compare(syntax.EQL, cycle, cycle)
	require(err != nil && strings.Contains(err.Error(), "maximum recursion depth"), "cyclic value should fail when reached")
	fmt.Println("PASS raw deep collision errors, membership projection, and cyclic-value masking")
}

func checkGrownDepthError() {
	deep, alias := wrap(starlark.MakeInt(0)), wrap(fromBits(0x8000000000000000))
	cycle := starlark.NewDict(0)
	require(cycle.SetKey(starlark.MakeInt(0), cycle) == nil, "growth cycle construction failed")

	left, right := starlark.NewDict(0), starlark.NewDict(0)
	require(left.SetKey(deep, cycle) == nil && right.SetKey(alias, cycle) == nil, "growth deep key insertion failed")
	for i := range 13 {
		if i == 7 || i == 12 {
			err := right.SetKey(deep, cycle)
			require(err != nil && strings.Contains(err.Error(), "maximum recursion depth") && right.Len() == i+1,
				"key depth error must precede growth at either threshold")
		}
		key := starlark.MakeInt(i)
		require(left.SetKey(key, cycle) == nil && right.SetKey(key, cycle) == nil, "growth filler insertion failed")
	}
	_, found, err := right.Get(deep)
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		"grown table lost raw lookup error")
	member, err := starlark.Binary(syntax.IN, deep, right)
	require(err == nil && member == starlark.False, "grown table did not mask membership lookup error")
	equal, err := starlark.Compare(syntax.EQL, left, right)
	require(err == nil && !equal, "grown table did not mask the cyclic value")
	fmt.Println("PASS threshold error precedes growth and grown lookup masks a cyclic value")
}

func expectProbeOrder(dict *starlark.Dict, word uint32, expected []int) {
	var visited []int
	_, found, err := dict.Get(traceKey{id: -1, word: word, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, expected),
		fmt.Sprintf("unexpected post-delete probe order %v, want %v (%v)", visited, expected, err))
}

func traceCollisions(count int) *starlark.Dict {
	dict := starlark.NewDict(0)
	for i := range count {
		require(dict.SetKey(traceKey{id: i, word: 3}, starlark.MakeInt(i)) == nil, "collision fixture insertion failed")
	}
	return dict
}

func checkDeletionSlots() {
	dict := traceCollisions(16)
	for _, deletion := range []struct {
		id      int
		reached []int
	}{
		{0, []int{7, 6, 5, 4, 3, 2, 1, 0}},
		{12, []int{7, 6, 5, 4, 3, 2, 1, 8, 15, 14, 13, 12}},
	} {
		var visited []int
		value, found, err := dict.Delete(traceKey{id: deletion.id, word: 3, visits: &visited})
		require(err == nil && found && value == starlark.MakeInt(deletion.id), "delete lost the selected value")
		require(slices.Equal(visited, deletion.reached), fmt.Sprintf("delete reached the wrong candidates %v", visited))
	}
	expectProbeOrder(dict, 3, []int{7, 6, 5, 4, 3, 2, 1, 8, 15, 14, 13, 11, 10, 9})
	for _, id := range []int{16, 0} {
		require(dict.SetKey(traceKey{id: id, word: 3}, starlark.MakeInt(99)) == nil, "hole reuse failed")
	}
	expectProbeOrder(dict, 3, []int{7, 6, 5, 4, 3, 2, 1, 0, 8, 15, 14, 13, 16, 11, 10, 9})
	want := []int{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 0}
	for i, key := range dict.Keys() {
		require(key.(traceKey).id == want[i], "hole reuse changed survivor iteration order")
	}

	// An empty overflow link remains. Reusing its last slots yields 10, 9.
	emptyLink := traceCollisions(9)
	_, found, err := emptyLink.Delete(traceKey{id: 8, word: 3})
	require(found && err == nil, "overflow-only removal failed")
	for _, id := range []int{9, 10} {
		require(emptyLink.SetKey(traceKey{id: id, word: 3}, starlark.MakeInt(id)) == nil, "empty overflow reuse failed")
	}
	expectProbeOrder(emptyLink, 3, []int{7, 6, 5, 4, 3, 2, 1, 0, 10, 9})

	// Advance the live count in the other home so the two old holes
	// survive until rehash. Rehash packs survivors in their original order.
	holey := traceCollisions(13)
	for _, id := range []int{0, 12} {
		_, found, err := holey.Delete(traceKey{id: id, word: 3})
		require(found && err == nil, "pre-growth delete failed")
	}
	for i := range 3 {
		id := 20 + i
		require(holey.SetKey(traceKey{id: id, word: 2}, starlark.MakeInt(id)) == nil, "post-delete grow failed")
	}
	expectProbeOrder(holey, 3, []int{8, 7, 6, 5, 4, 3, 2, 1, 9, 11, 10})
	for i, key := range holey.Keys() {
		id := i + 1
		if i >= 11 {
			id = i + 9
		}
		require(key.(traceKey).id == id, "rehash changed survivor iteration order")
	}

	// Ordinary numeric values exercise alias deletion and the newly stored key.
	numeric := starlark.NewDict(0)
	zeroAlias := fromBits(0x8000000000000000)
	require(numeric.SetKey(starlark.MakeInt(0), starlark.MakeInt(17)) == nil &&
		numeric.SetKey(starlark.MakeInt64(1<<32), starlark.MakeInt(21)) == nil, "numeric delete setup failed")
	value, found, err := numeric.Delete(zeroAlias)
	require(err == nil && found && value == starlark.MakeInt(17), "numeric alias deletion failed")
	require(numeric.SetKey(zeroAlias, starlark.MakeInt(99)) == nil, "numeric alias reinsertion failed")
	first, fits := numeric.Keys()[0].(starlark.Int).Int64()
	require(fits && first == 1<<32 &&
		math.Float64bits(float64(numeric.Keys()[1].(starlark.Float))) == 0x8000000000000000,
		"numeric alias did not enter at the tail with its own identity")
	fmt.Println("PASS primary and overflow holes, retained empty links, highest-slot reuse, survivor rehash and alias reinsertion")
}

func checkDeletionErrors() {
	dict := starlark.NewDict(0)
	deep := wrap(starlark.MakeInt64(1 << 32))
	require(dict.SetKey(deep, starlark.MakeInt(7)) == nil, "delete depth setup failed")
	before := dict.Keys()
	value, found, err := dict.Delete(starlark.MakeInt(0))
	require(value == starlark.None && !found && err == nil, "missing delete did not return None")
	_, found, err = dict.Delete(starlark.NewList(nil))
	require(!found && err != nil && strings.Contains(err.Error(), "unhashable"), "delete must report a hash error")
	_, found, err = dict.Delete(wrap(starlark.MakeInt(0)))
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		"delete must report the first reached depth error")
	require(dict.Len() == 1 && dict.Keys()[0].String() == before[0].String(), "miss or error changed the table")

	var calls int
	query := traceKey{id: 42, word: 3, hashCalls: &calls}
	iterator := dict.Iterate()
	_, _, err = dict.Delete(query)
	require(err != nil && strings.Contains(err.Error(), "during iteration") && calls == 0,
		"iterator guard must precede hashing")
	iterator.Done()
	dict.Freeze()
	_, _, err = dict.Delete(query)
	require(err != nil && strings.Contains(err.Error(), "frozen") && calls == 0, "freeze guard must precede hashing")
	var zero starlark.Dict
	_, found, err = zero.Delete(query)
	require(!found && err == nil && calls == 0, "unallocated Go table must return before hashing")
	_, found, err = starlark.NewDict(0).Delete(query)
	require(!found && err == nil && calls == 1, "initialized empty Go table must hash the key")
	fmt.Println("PASS delete miss, hash/depth errors, and pre-hash guards outside the admitted profile")
}

func checkScalarAbstraction() {
	dict := starlark.NewDict(0)
	var keys []starlark.Value
	for i := range 9 {
		keys = append(keys, starlark.MakeInt(i))
	}
	keys = append(keys, starlark.MakeInt64(1<<32), starlark.False, fromBits(0x7ff8000000000007),
		starlark.MakeInt64(9007199254740993), fromBits(0x4340000000000000))
	for i, key := range keys {
		require(dict.SetKey(key, starlark.MakeInt(i)) == nil, "scalar abstraction insert failed")
	}
	negativeZero, otherNaN := fromBits(0x8000000000000000), fromBits(0xfff8000000000015)
	require(dict.SetKey(negativeZero, starlark.MakeInt(100)) == nil &&
		dict.SetKey(otherNaN, starlark.MakeInt(101)) == nil, "scalar alias replacement failed")
	require(dict.Len() == len(keys), "scalar alias replacement changed the row count")
	for i, stored := range dict.Keys() {
		switch key := keys[i].(type) {
		case starlark.Float:
			got, ok := stored.(starlark.Float)
			require(ok && math.Float64bits(float64(got)) == math.Float64bits(float64(key)), "float key identity changed")
		default:
			require(stored == key, "original scalar key or iteration order changed")
		}
	}
	for _, tc := range []struct {
		key  starlark.Value
		want int
	}{
		{negativeZero, 100}, {starlark.MakeInt64(1 << 32), 9}, {starlark.False, 10}, {starlark.True, -1},
		{otherNaN, 101}, {starlark.MakeInt64(9007199254740993), 12}, {starlark.MakeInt64(9007199254740992), 13},
		{starlark.MakeInt(42), -1},
	} {
		value, found, err := dict.Get(tc.key)
		require(err == nil && found == (tc.want >= 0), "wrong scalar abstraction lookup result")
		if found {
			require(value == starlark.MakeInt(tc.want), "wrong scalar abstraction value")
		}
	}
	fmt.Println("PASS scalar abstraction observations, exact large numbers and stored alias identity")
}

type failingHashKey struct{ calls *int }

func (failingHashKey) String() string       { return "failing_hash" }
func (failingHashKey) Type() string         { return "failing_hash" }
func (failingHashKey) Freeze()              {}
func (failingHashKey) Truth() starlark.Bool { return starlark.True }
func (k failingHashKey) Hash() (uint32, error) {
	*k.calls++
	return 0, fmt.Errorf("hash was reached")
}

func checkMutationGuards() {
	var calls int
	bad := failingHashKey{calls: &calls}
	value := starlark.MakeInt(7)
	var zero starlark.Dict
	_, found, err := zero.Delete(bad)
	require(!found && err == nil && calls == 0, "zero delete must miss before hashing")

	iterator := zero.Iterate()
	err = zero.SetKey(bad, value)
	require(err != nil && err.Error() == "cannot insert into hash table during iteration" && calls == 0,
		"iterator guard must precede initialization and hashing")
	_, _, err = zero.Delete(bad)
	require(err != nil && err.Error() == "cannot delete from hash table during iteration" && calls == 0,
		"iterator guard must precede the zero-table delete miss")
	iterator.Done()
	_, found, err = zero.Delete(bad)
	require(!found && err == nil && calls == 0, "rejected assignment allocated its table")

	err = zero.SetKey(bad, value)
	require(err != nil && err.Error() == "hash was reached" && calls == 1 && zero.Len() == 0,
		"allowed zero assignment must hash and leave its rows empty on error")
	_, found, err = zero.Delete(bad)
	require(!found && err != nil && err.Error() == "hash was reached" && calls == 2,
		"failed zero assignment must leave allocated storage")
	_, found, err = starlark.NewDict(0).Delete(bad)
	require(!found && err != nil && err.Error() == "hash was reached" && calls == 3,
		"initialized empty delete must hash")

	dict := starlark.NewDict(0)
	existing := traceKey{id: 0, word: 3, hashCalls: &calls}
	require(dict.SetKey(existing, value) == nil, "replacement guard setup failed")
	n := calls
	iterator = dict.Iterate()
	err = dict.SetKey(existing, starlark.None)
	require(err != nil && err.Error() == "cannot insert into hash table during iteration" && calls == n,
		"iteration must reject replacement before hashing")
	dict.Freeze()
	err = dict.SetKey(existing, starlark.None)
	require(err != nil && err.Error() == "cannot insert into frozen hash table" && calls == n,
		"freeze must win over active iteration on assignment")
	_, _, err = dict.Delete(bad)
	require(err != nil && err.Error() == "cannot delete from frozen hash table" && calls == n,
		"freeze must win over active iteration on deletion")
	iterator.Done()
	got, found, err := dict.Get(existing)
	require(err == nil && found && got == value && dict.Len() == 1, "a rejected edit changed the dictionary")

	var frozenZero starlark.Dict
	frozenZero.Freeze()
	n = calls
	_, _, err = frozenZero.Delete(bad)
	require(err != nil && err.Error() == "cannot delete from frozen hash table" && calls == n,
		"freeze must win over the unallocated delete miss")
	popitem, err := frozenZero.Attr("popitem")
	require(err == nil, "missing popitem")
	_, err = starlark.Call(&starlark.Thread{}, popitem, nil, nil)
	require(err != nil && err.Error() == "popitem: empty dict", "popitem must check emptiness before deletion guards")
	fmt.Println("PASS guard precedence, retained rows, zero-table initialization, and the popitem boundary")
}

func checkAssignmentOperandOrder() {
	var trace []string
	var hashes int
	var keyError bool
	frozen := starlark.NewDict(0)
	frozen.Freeze()
	note := func(name string, value starlark.Value) *starlark.Builtin {
		return starlark.NewBuiltin(name, func(_ *starlark.Thread, _ *starlark.Builtin, _ starlark.Tuple, _ []starlark.Tuple) (starlark.Value, error) {
			trace = append(trace, name)
			if name == "key" && keyError {
				return nil, fmt.Errorf("key expression failed")
			}
			return value, nil
		})
	}
	env := starlark.StringDict{
		"rhs": note("rhs", starlark.MakeInt(7)), "receiver": note("receiver", frozen),
		"key": note("key", failingHashKey{calls: &hashes}),
	}
	run := func(source, errorPart string, order []string) {
		trace = nil
		_, err := starlark.ExecFileOptions(&syntax.FileOptions{}, &starlark.Thread{}, "guards.star", source, env)
		require(err != nil && strings.Contains(err.Error(), errorPart),
			fmt.Sprintf("want %q, got %v", errorPart, err))
		require(slices.Equal(trace, order) && hashes == 0,
			fmt.Sprintf("want stages %v without hashing, got %v with %d hashes", order, trace, hashes))
	}
	run("receiver()[key()] = rhs()", "cannot insert into frozen hash table", []string{"rhs", "receiver", "key"})
	keyError = true
	run("receiver()[key()] = rhs()", "key expression failed", []string{"rhs", "receiver", "key"})
	run("def missing():\n  d[key()] = rhs()\n  d = {}\nmissing()\n",
		"referenced before assignment", []string{"rhs"})
	fmt.Println("PASS assignment evaluates RHS, receiver and key before guarding the mutation")
}

func main() {
	require(starlark.CompareLimit == 10, "pinned default comparison limit changed")
	checkHashes()
	checkSlots()
	checkGrowth()
	checkSecondRehash()
	checkDepthError()
	checkGrownDepthError()
	checkDeletionSlots()
	checkDeletionErrors()
	checkScalarAbstraction()
	checkMutationGuards()
	checkAssignmentOperandOrder()
}

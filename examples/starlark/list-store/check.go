// Run from the pinned starlark-go checkout as documented in docs/projects/starlark-lists.md.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

// Init exposes the heap before publication, including effects preceding an error.
func run(source string) (starlark.StringDict, error) {
	predeclared := starlark.StringDict{}
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "list_store.star", source+"\n", predeclared.Has,
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "list store"}, predeclared)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func requireError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want error %q, got %v", part, err))
}

func checkAliases() {
	globals, err := run(`x = [10]
y = x
other = [10]
appended = x.append(11)
y[-1] = 12
observed = x[-1]
independent = other[0]`)
	require(err == nil, fmt.Sprint(err))
	require(globals["x"] == globals["y"] && globals["x"] != globals["other"], "unexpected list identities")
	require(globals["appended"] == starlark.None, "append must return None")
	require(globals["observed"].String() == "12" && globals["independent"].String() == "10",
		"alias write or independent allocation")
	fmt.Println("PASS fresh list addresses, alias write, negative indexing and append result")
}

func checkFreeze() {
	globals, err := run(`leaf = [42]
inner = [leaf]
outer = [inner]
alias = inner
spare = []
inner.append(outer)
inner.append(inner)`)
	require(err == nil, fmt.Sprint(err))
	outer := globals["outer"].(*starlark.List)
	inner := globals["inner"].(*starlark.List)
	alias := globals["alias"].(*starlark.List)
	leaf := globals["leaf"].(*starlark.List)
	spare := globals["spare"].(*starlark.List)
	outer.Freeze()
	outer.Freeze()
	require(outer.Index(0) == alias && alias == inner, "alias edges changed during freeze")
	require(inner.Index(1) == outer && inner.Index(2) == inner, "cycle edges changed during freeze")
	requireError(alias.Append(starlark.None), "frozen list")
	requireError(inner.SetIndex(2, starlark.None), "frozen list")
	requireError(leaf.Append(starlark.None), "frozen list")
	require(leaf.Index(0).String() == "42", "frozen list read")
	require(spare.Append(starlark.MakeInt(5)) == nil, "unreachable list was frozen")
	fmt.Println("PASS nested reachability, mutual cycle, self-cycle, frozen aliases and unrelated mutable list")
}

func checkEvaluationOrder() {
	for _, tc := range []struct {
		source, err, elements string
	}{
		{`a = []
a[0][0] = a.append(9)`, "does not support item assignment", "[9]"},
		{`a = []
out = [a.append(4), a[4], a.append(5)]`, "out of range", "[4]"},
		{`a = []
(1).append(a.append(9))`, "no .append field or method", "[]"},
	} {
		globals, err := run(tc.source)
		requireError(err, tc.err)
		require(globals["a"].String() == tc.elements, "unexpected state after error")
	}
	fmt.Println("PASS RHS-first assignment, left-to-right elements and method lookup before arguments")
}

func checkIndexErrors() {
	for _, tc := range []struct {
		source, err string
	}{
		{"out = [10][-2]", "out of range"},
		{"out = [10][True]", "list index:"},
		{"out = [10][18446744073709551616]", "list index:"},
		{"out = (1)[0]", "unhandled index operation"},
	} {
		_, err := run(tc.source)
		requireError(err, tc.err)
	}
	fmt.Println("PASS negative bounds, Boolean index, very large index and scalar receiver errors")
}

func checkIteration() {
	globals, err := run(`def controls(a, out):
    for x in a:
        if x:
            out.append(x)
            continue
        break
    a.append(7)
    return x

def exhausted(a):
    for x in a:
        continue
    a.append(7)
    return x

def guarded(a, alias, out):
    for x in a:
        for y in alias:
            break
        out.append(x)
        alias[0] = 9

def nested_append(a, alias):
    for x in a:
        for y in alias:
            alias.append(9)

def nested_error(a, alias, out):
    for x in a:
        for y in alias:
            out[0]

def returned(a, b):
    for x in a:
        for y in b:
            return y
`)
	require(err == nil, fmt.Sprint(err))
	call := func(name string, args ...starlark.Value) (starlark.Value, error) {
		return starlark.Call(&starlark.Thread{Name: name}, globals[name], args, nil)
	}
	input := func() *starlark.List {
		return starlark.NewList([]starlark.Value{starlark.MakeInt(1), starlark.MakeInt(0), starlark.MakeInt(2)})
	}
	a, out := input(), starlark.NewList(nil)
	result, err := call("controls", a, out)
	require(err == nil && result.String() == "0" && a.String() == "[1, 0, 2, 7]" &&
		out.String() == "[1]", "break/continue or post-break mutation")
	a = input()
	result, err = call("exhausted", a)
	require(err == nil && result.String() == "2" && a.String() == "[1, 0, 2, 7]", "exhaustion cleanup")
	a, out = input(), starlark.NewList(nil)
	_, err = call("guarded", a, a, out)
	requireError(err, "during iteration")
	require(out.String() == "[1]" && a.Append(starlark.MakeInt(9)) == nil,
		"inner break must preserve outer guard, failure must release it")
	a = input()
	_, err = call("nested_append", a, a)
	requireError(err, "during iteration")
	require(a.Append(starlark.MakeInt(9)) == nil, "same-object nested guard cleanup")
	a = input()
	_, err = call("nested_error", a, a, starlark.NewList(nil))
	requireError(err, "out of range")
	require(a.Append(starlark.MakeInt(9)) == nil, "ordinary nested error cleanup")
	a, b := input(), starlark.NewList([]starlark.Value{starlark.MakeInt(12)})
	result, err = call("returned", a, b)
	require(err == nil && result.String() == "12" &&
		a.Append(starlark.None) == nil && b.Append(starlark.None) == nil, "nested return cleanup")
	fmt.Println("PASS break/continue, exhaustion, alias guards and iterator cleanup after errors and return")
}

func checkDictionary() {
	globals, err := run(`key = ((), (True, 1), None)
d = {(True,): 10, (1,): 20, key: 30}
alias = d
alias[((), (True, 1), None)] = 42
hit = d[key]
true_key = d[(True,)]
int_key = d[(1,)]
last = (1, 2)[-1]
`)
	require(err == nil, fmt.Sprint(err))
	require(globals["hit"].String() == "42" && globals["true_key"].String() == "10" &&
		globals["int_key"].String() == "20" && globals["last"].String() == "2",
		"tuple key comparison or tuple indexing")
	_, err = run("(1,)[0] = 2")
	requireError(err, "does not support item assignment")
	_, err = run("out = {}[2]")
	requireError(err, "key 2 not in dict")
	_, err = run("out = {([],): 0}")
	requireError(err, "unhashable type: list")
	globals, err = run(`a = []
out = {(1,): a.append(1), (1,): a.append(2), (2,): a.append(3)}`)
	requireError(err, "duplicate key")
	require(globals["a"].String() == "[1, 2]", "duplicate key evaluation order")
	fmt.Println("PASS tuple key structure, Boolean/integer distinction, bounds, key errors and duplicate order")

	globals, err = run(`leaf = []
d = {}
root = (d,)
d[1] = leaf
leaf.append(root)
spare = []
`)
	require(err == nil, fmt.Sprint(err))
	globals["root"].Freeze()
	d := globals["d"].(*starlark.Dict)
	leaf := globals["leaf"].(*starlark.List)
	spare := globals["spare"].(*starlark.List)
	retained, found, err := d.Get(starlark.MakeInt(1))
	require(err == nil && found && retained == leaf, "frozen dictionary lost its list reference")
	requireError(leaf.Append(starlark.None), "frozen list")
	requireError(d.SetKey(leaf, starlark.None), "frozen hash table")
	_, _, err = d.Get(leaf)
	requireError(err, "unhashable type: list")
	_, _, err = d.Get(d)
	requireError(err, "unhashable type: dict")
	require(spare.Append(starlark.None) == nil, "unreachable list was frozen")
	fmt.Println("PASS freeze across a tuple/dictionary/list cycle and frozen-key policy")

	globals, err = run(`def iterate(d, out):
    for x in (8, 9):
        out.append(x)
    for k in d:
        out.append(k)

def guard(d, alias):
    for k in d:
        alias[k] = 0

d = {3: 10, 1: 20}
d[3] = 11
d[2] = 12
`)
	require(err == nil, fmt.Sprint(err))
	d, out := globals["d"].(*starlark.Dict), starlark.NewList(nil)
	thread := &starlark.Thread{Name: "collections"}
	_, err = starlark.Call(thread, globals["iterate"], starlark.Tuple{d, out}, nil)
	require(err == nil && out.String() == "[8, 9, 3, 1, 2]", "tuple and dictionary iteration order")
	_, err = starlark.Call(thread, globals["guard"], starlark.Tuple{d, d}, nil)
	requireError(err, "during iteration")
	require(d.SetKey(starlark.MakeInt(3), starlark.MakeInt(9)) == nil, "dictionary iterator cleanup")
	fmt.Println("PASS tuple iteration, ordered dictionary updates and dictionary alias guards with cleanup")
}

func main() {
	checkAliases()
	checkFreeze()
	checkEvaluationOrder()
	checkIndexErrors()
	checkIteration()
	checkDictionary()
}

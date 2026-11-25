// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func run(src string) (starlark.StringDict, error) {
	predeclared := starlark.StringDict{}
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "functions.star", src+"\n", predeclared.Has,
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "functions"}, predeclared)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func checkError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want %q, got %v", part, err))
}

func checkClosure() {
	g, err := run(`def factory(x):
    def get():
        return x
    before = get()
    x = 2
    return (before, get)
pair = factory(1)
out = pair[1]()
`)
	require(err == nil && g["out"].String() == "2" && g["pair"].(starlark.Tuple)[0].String() == "1",
		"closure did not retain the defining cell")
	g, err = run(`def get():
    return x
x = 42
def caller(x):
    return get()
out = caller(9)`)
	require(err == nil && g["out"].String() == "42", "call did not preserve lexical globals")
	_, err = run(`def get():
    return x
out = get()
x = 42`)
	checkError(err, "referenced before assignment")
	fmt.Println("PASS live lexical cells, escaped closures, and defining-module global slots")
}

func checkReentry() {
	g, err := run(`def maker(other):
    def f(x):
        return other(x)
    return f
def leaf(x):
    return x
b = maker(leaf)
a = maker(b)
out = a(1)`)
	checkError(err, "function f called recursively")
	require(g["a"] != g["b"], "the two function instances should differ")
	fmt.Println("PASS default recursion guard checks declaration identity")
}

func checkStoreAndFreeze() {
	g, err := run(`def f(xs):
    xs.append(7)
    return xs[12]
container = []
out = f(container)`)
	checkError(err, "out of range")
	require(g["container"].String() == "[7]", "effects before failure were lost")
	g, err = run(`def factory():
    xs = []
    def appender():
        xs.append(1)
    return appender
f = factory()`)
	require(err == nil, fmt.Sprint(err))
	g["f"].Freeze()
	_, err = starlark.Call(&starlark.Thread{Name: "frozen closure"}, g["f"], nil, nil)
	checkError(err, "frozen list")
	fmt.Println("PASS effects survive failure and freezing follows captured cells")
}

func checkArguments() {
	g, err := run(`def f(a, b=2, *rest, c, d=4, **kw):
    return (a, b, rest, c, d, kw)
out = f(1, c=5, y=9, *[3, 7], **{"z": 8})`)
	require(err == nil && g["out"].String() == `(1, 3, (7,), 5, 4, {"y": 9, "z": 8})`,
		"positional, keyword-only or packed arguments")
	prefix := "def f(a, b=2, *rest, c, d=4, **kw): pass\n"
	for _, test := range []struct{ call, error string }{
		{"f(1)", "missing 1 argument (c)"},
		{"f(1, a=2)", `multiple values for parameter "a"`},
		{`f(1, c=2, **{"c": 3})`, `multiple values for parameter "c"`},
		{`f(x=2, **{"x": 3})`, `multiple values for parameter "x"`},
		{"f(*1)", "argument after * must be iterable"},
		{"f(**[])", "argument after ** must be a mapping"},
		{"f(*1, **{3: 7})", "keywords must be strings"},
		{"f(c=1, c=2)", "keyword argument"},
	} {
		_, err := run(prefix + test.call)
		checkError(err, test.error)
	}
	_, err = run(`def f(a, *, b=2, c): pass
f(1, 2)`)
	checkError(err, "accepts 1 positional argument")
	_, err = run(`def f(a, *, b=2, c): pass
f(1, other=2)`)
	checkError(err, "unexpected keyword argument")
	g, err = run(prefix + `events = []
f(events.append(1), c=events.append(2), *[events.append(3)], **{3: events.append(4)})`)
	checkError(err, "keywords must be strings")
	require(g["events"].String() == "[1, 2, 3, 4]", "operand effects must precede expansion errors")
	fmt.Println("PASS complete argument packs, operand ordering, and argument errors")
}

func checkDefaults() {
	g, err := run(`counter = []
def f(xs=[], stamp=counter.append(4)):
    xs.append(1)
    return xs
a = f()
b = f()`)
	require(err == nil && g["a"] == g["b"] && g["b"].String() == "[1, 1]" &&
		g["counter"].String() == "[4]", "defaults did not run once or were copied")
	g["f"].Freeze()
	_, err = starlark.Call(&starlark.Thread{Name: "frozen defaults"}, g["f"], nil, nil)
	checkError(err, "frozen list")
	fmt.Println("PASS definition-time defaults share identity and freeze with their function")

	g, err = run(`def f(*, x): return x
out = f(x=3)`)
	require(err == nil && g["out"].String() == "3", "unexpected pinned Go bare-star rule")
	fmt.Println("NOTE pinned Go accepts required-only bare-star signatures, unlike the pinned prose")
}

func main() {
	checkClosure()
	checkReentry()
	checkStoreAndFreeze()
	checkArguments()
	checkDefaults()
}

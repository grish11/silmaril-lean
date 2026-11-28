// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func run(src string) (starlark.StringDict, error) {
	_, program, err := starlark.SourceProgramOptions(
		&syntax.FileOptions{}, "builtins.star", src+"\n", func(string) bool { return false },
	)
	if err != nil {
		return nil, err
	}
	return program.Init(&starlark.Thread{Name: "builtins"}, nil)
}

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func checkError(err error, part string) {
	require(err != nil && strings.Contains(err.Error(), part), fmt.Sprintf("want %q, got %v", part, err))
}

func checkPureBuiltins() {
	g, err := run(`def apply(abs, x):
    return abs(x)
magnitude = abs
some = any
every = all
out = (apply(magnitude, -1000000000000000000000000000000), abs(0), abs(7),
       some([]), every(()), some([0, None, [], "x"]), every((1, [], 2)),
       some({0: True}), every({"x": False}), some(range(0)), every(range(0)),
       some(range(0, 7)), every(range(0, 7)), every(range(5, 1, -2)),
       some(*[[0, abs]], **{}), {any: "quantifier"}[some])`)
	require(err == nil, fmt.Sprint(err))
	want := `(1000000000000000000000000000000, 0, 7, False, True, True, False, False, True, False, True, True, False, True, True, "quantifier")`
	require(g["out"].String() == want, fmt.Sprintf("want %s, got %s", want, g["out"]))
	fmt.Println("PASS exact integer abs, first-class aliases, and ordered truth on list, tuple, dict and range")

	const setup = `def note(label, value):
    events.append(label)
    return value
events = []
out = [99]
`
	for _, tc := range []struct{ call, want, effects string }{
		{"abs()", "want 1", "[]"},
		{"any()", "want 1", "[]"},
		{"all()", "want 1", "[]"},
		{"abs(True)", "want int or float", "[]"},
		{`all("x")`, "want iterable", "[]"},
		{"any(None)", "want iterable", "[]"},
		{"note(1, any)(note(2, 0), note(3, 1), ignored=note(4, 0))", "unexpected keyword arguments", "[1, 2, 3, 4]"},
		{"all(note(1, 0), note(2, []))", "want 1", "[1, 2]"},
		{"any(*note(1, 0), **note(2, {\"x\": 1}))", "argument after * must be iterable", "[1, 2]"},
		{"all(note(1, 0), len(note(2, 0)), ignored=note(3, 0))", "has no len", "[1, 2]"},
	} {
		g, err := run(setup + "out[0] = " + tc.call)
		checkError(err, tc.want)
		require(g["out"].String() == "[99]" && g["events"].String() == tc.effects, fmt.Sprint(g))
	}
	fmt.Println("PASS callee and operand effects precede spread, keyword, arity and type failures")
}

// Host probes record Go callbacks. They are outside the Lean value profile.
type truthProbe struct {
	starlark.Value
	flag  starlark.Bool
	trace *[]string
}

func (p truthProbe) Truth() starlark.Bool {
	*p.trace = append(*p.trace, p.flag.String())
	return p.flag
}

type iteratorProbe struct {
	starlark.Value
	flags []starlark.Bool
	trace *[]string
}

func (p *iteratorProbe) Iterate() starlark.Iterator {
	*p.trace = append(*p.trace, "Iterate")
	return p
}

func (p *iteratorProbe) Next(value *starlark.Value) bool {
	*p.trace = append(*p.trace, "Next")
	if len(p.flags) == 0 {
		return false
	}
	*value = truthProbe{starlark.None, p.flags[0], p.trace}
	p.flags = p.flags[1:]
	return true
}

func (p *iteratorProbe) Done() { *p.trace = append(*p.trace, "Done") }

func checkGoBoundary() {
	g, err := run(`out = (abs(-1.25), any("x".elems()))`)
	require(err == nil, fmt.Sprint(err))
	require(g["out"].String() == "(1.25, True)", fmt.Sprint(g["out"]))
	for _, tc := range []struct {
		name  string
		flags []starlark.Bool
		want  starlark.Bool
		trace string
	}{
		{"any", []starlark.Bool{false, true, false}, true, "Iterate Next False Next True Done"},
		{"all", []starlark.Bool{true, false, true}, false, "Iterate Next True Next False Done"},
		{"all", nil, true, "Iterate Next Done"},
	} {
		var trace []string
		p := &iteratorProbe{starlark.None, tc.flags, &trace}
		result, err := starlark.Call(&starlark.Thread{}, starlark.Universe[tc.name], starlark.Tuple{p}, nil)
		require(err == nil && result == tc.want && strings.Join(trace, " ") == tc.trace,
			fmt.Sprintf("%s: value %v, error %v, trace %v", tc.name, result, err, trace))
	}
	fmt.Println("PASS Go-only float and string-view inputs, and host iterator cutoff and cleanup")
}

func main() {
	checkPureBuiltins()
	checkGoBoundary()
}

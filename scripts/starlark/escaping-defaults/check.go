// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func main() {
	opts := &syntax.FileOptions{}
	const success = `def maker(seed):
    def inner(seed, value=seed, buffer=[1]):
        return value
    seed = 91
    return inner
saved_seed = [3]
escaped = maker(saved_seed)
saved = escaped
first = saved(0)
replacement = [4]
override = saved(0, replacement)
again = escaped(0)
`
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "escape.star", success, nil)
	require(err == nil, err)
	require(globals["escaped"] == globals["saved"] && globals["first"] == globals["saved_seed"] &&
		globals["again"] == globals["saved_seed"] && globals["first"].String() == "[3]" &&
		globals["override"] == globals["replacement"] && globals["override"].String() == "[4]", globals)
	err = globals["saved_seed"].(*starlark.List).SetIndex(0, starlark.MakeInt(5))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS saved child defaults survive rebinding and escape, explicit arguments override, and publication freezes")

	const failure = `def maker(seed):
    def inner(seed, kept=[1], value=seed[1], skipped=[3]):
        return value
    seed = 91
    return inner
saved_seed = [3]
escaped = maker(saved_seed)
saved = escaped
first = saved(0)
`
	_, program, err := starlark.SourceProgramOptions(opts, "failure.star", failure, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "list index 1 out of range"), err)
	require(partial["escaped"] == nil && partial["saved"] == nil && partial["first"] == nil &&
		partial["saved_seed"].String() == "[3]", partial)
	fmt.Println("PASS failed nested default prevents child escape and skips the rest of the module")
}

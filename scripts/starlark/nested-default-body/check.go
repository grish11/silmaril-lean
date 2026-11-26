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

const prefix = `def make(seed, offset):
    def inner(saved=seed):
        cache = [31]
        picked = saved[offset]
        buffer = [picked]
        answer = buffer[seed]
        repeat_read = saved[offset]
        after = [41]
        return answer
    seed = 0
    return inner
seed_a = [3, 5]
seed_b = [6, 8]
a = make(seed_a, 1)
b = make(seed_b, 0)
alias = a
first = alias()
second = b()
`

const suffix = `override = a(replacement)
again = alias()
`

func checkPrefix(globals starlark.StringDict) {
	require(globals["a"] == globals["alias"] && globals["a"] != globals["b"] &&
		globals["first"].String() == "5" && globals["second"].String() == "6", globals)
}

func main() {
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "nested.star",
		prefix+"replacement = [7, 9]\n"+suffix, nil)
	require(err == nil, err)
	checkPrefix(globals)
	require(globals["override"].String() == "9" && globals["again"].String() == "5", globals)
	err = globals["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS separate escaping activations with two captured parameters, live rebinding alongside saved defaults, override and freezing")

	_, program, err := starlark.SourceProgramOptions(opts, "nested-error.star",
		prefix+"replacement = [7]\n"+suffix, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "list index 1 out of range"), err)
	checkPrefix(partial)
	require(partial["override"] == nil && partial["again"] == nil, partial)
	fmt.Println("PASS an index error after earlier escaped calls retains their results and skips the destination and later call")
}

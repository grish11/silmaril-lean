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

const prefix = `start = 1
def score(offset=start):
    cache = [31]
    copy = offset
    result = table[copy]
    after = [41]
    return result
saved = score
`

func main() {
	opts := &syntax.FileOptions{}
	const initialized = "table = [9, 11]\nfirst = saved()\nsecond = score(0)\n"
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "body.star", prefix+initialized, nil)
	require(err == nil, err)
	require(globals["score"] == globals["saved"] && globals["first"].String() == "11" &&
		globals["second"].String() == "9", globals)
	err = globals["table"].(*starlark.List).SetIndex(0, starlark.MakeInt(5))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS ordered body reads see the initialized module slot, and saved versus explicit positions return 11 and 9")

	const uninitialized = "first = saved()\ntable = [9, 11]\nsecond = score(0)\n"
	_, program, err := starlark.SourceProgramOptions(opts, "body-error.star",
		prefix+uninitialized, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(new(starlark.Thread), nil)
	require(err != nil && strings.Contains(err.Error(), "global variable table referenced before assignment"), err)
	require(partial["first"] == nil && partial["second"] == nil && partial["table"] == nil &&
		partial["saved"] == partial["score"], partial)
	fmt.Println("PASS first reached captured read error prevents the call assignment and the remaining module commands")
}

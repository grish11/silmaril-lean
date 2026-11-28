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

func program(index int, defaultRead string, initializeTable, initializeSetting bool) string {
	first := fmt.Sprintf("a = make(%d)\n", index)
	const table = "table = outer_a\n"
	const setting = "setting = 1\n"
	if initializeSetting {
		first = setting + first
	} else {
		first += setting
	}
	if initializeTable {
		first = table + first
	} else {
		first += table
	}
	return fmt.Sprintf(`def make(seed):
    earlier = [13]
    shadow = seed
    offset = table[shadow]
    def inner(early=[14], saved=%s, setting_at_def=setting, shadow_at_def=shadow, last=[73]):
        picked = saved[offset]
        buffer = [[saved[setting_at_def]]]
        answer = buffer[shadow_at_def][seed]
        repeat_read = saved[offset]
        return answer
    seed = 0
    offset = 0
    unused = 42
    offset = 1
    return inner
shadow = 99
seed_a = [3, 5]
seed_b = [6, 8]
outer_a = [seed_a]
%smake_alias = make
def edit(index):
    index, table[index] = patch
    return index
patch = (0, seed_b)
touched = edit(0)
b = make_alias(0)
alias = a
first = alias()
second = b()
replacement = [7, 9]
override = a(0, replacement)
again = alias()
`, defaultRead, first)
}

func checkFailure(opts *syntax.FileOptions, source string, errorParts ...string) starlark.StringDict {
	_, compiled, err := starlark.SourceProgramOptions(opts, "wrapper-error.star",
		source, func(string) bool { return false })
	require(err == nil, err)
	partial, err := compiled.Init(new(starlark.Thread), nil)
	require(err != nil, partial)
	for _, part := range errorParts {
		require(strings.Contains(err.Error(), part), err)
	}
	require(partial["seed_a"].String() == "[3, 5]" && partial["seed_b"].String() == "[6, 8]" &&
		partial["a"] == nil && partial["b"] == nil && partial["make_alias"] == nil &&
		partial["alias"] == nil && partial["first"] == nil, partial)
	err = partial["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err == nil, err)
	return partial
}

func main() {
	opts := &syntax.FileOptions{}
	globals, err := starlark.ExecFileOptions(opts, new(starlark.Thread), "wrapper.star", program(0, "offset", true, true), nil)
	require(err == nil, err)
	require(globals["a"] == globals["alias"] && globals["a"] != globals["b"] &&
		globals["make"] == globals["make_alias"] && globals["shadow"].String() == "99" &&
		globals["table"] == globals["outer_a"] && globals["table"].String() == "[[6, 8]]" &&
		globals["touched"].String() == "0" && globals["first"].String() == "5" &&
		globals["second"].String() == "8" && globals["override"].String() == "9" &&
		globals["again"].String() == "5", globals)
	err = globals["seed_a"].(*starlark.List).SetIndex(0, starlark.MakeInt(0))
	require(err != nil && strings.Contains(err.Error(), "frozen"), err)
	fmt.Println("PASS direct module and shadowed local defaults, with live prefix reads and saved values across calls")

	partial := checkFailure(opts, program(0, "offset", false, true), "global variable table", "before assignment")
	require(partial["table"] == nil, partial)
	fmt.Println("PASS a reached uninitialized module read stops before default evaluation and publication")

	checkFailure(opts, program(1, "offset", true, true), "index 1 out of range")
	fmt.Println("PASS initialized module read can reach the later index failure")

	checkFailure(opts, program(0, "unused", true, true), "unused", "before assignment")
	fmt.Println("PASS successful prefix leaves the suffix-only local uninitialized during defaults")

	partial = checkFailure(opts, program(0, "offset", true, false), "global variable setting", "before assignment")
	require(partial["table"] == partial["outer_a"] && partial["setting"] == nil, partial)
	fmt.Println("PASS a direct module default fails after the prefix and before child installation")
}

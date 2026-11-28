// Run from the pinned Starlark-Go checkout with go run and this file's path.
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

func source(mapping string) string {
	return fmt.Sprintf(`data = [31]
def worker(first, *rest, key=data, **extras):
    marked = [44]
    print(marked[0])
    probe = key[0]
    return late
late = data
copy = worker
result = copy([17], extra=[61], *[data], **%s)
after = [99]
`, mapping)
}

func main() {
	opts := &syntax.FileOptions{}
	var events []string
	thread := &starlark.Thread{Print: func(_ *starlark.Thread, msg string) { events = append(events, msg) }}
	globals, err := starlark.ExecFileOptions(opts, thread, "published-checked.star", source(`{"key": data}`), nil)
	require(err == nil, err)
	require(globals["worker"] == globals["copy"] && globals["data"] == globals["result"] &&
		globals["after"].String() == "[99]" && strings.Join(events, ",") == "44", globals)
	require(globals["data"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, globals)
	fmt.Println("PASS published closure aliases keep original values and publication freezes the shared list")

	for _, test := range []struct {
		mapping, errorText, events string
	}{
		{`{"key": 8}`, "unhandled index operation", "44"},
		{`{"extra": [62]}`, `multiple values for parameter "extra"`, ""},
	} {
		events = nil
		_, program, err := starlark.SourceProgramOptions(opts, "unpublished-checked.star",
			source(test.mapping), func(string) bool { return false })
		require(err == nil, err)
		partial, err := program.Init(thread, nil)
		require(err != nil && strings.Contains(err.Error(), test.errorText), err)
		require(partial["result"] == nil && partial["after"] == nil && partial["copy"] == partial["worker"] &&
			partial["data"].String() == "[31]" && strings.Join(events, ",") == test.events, partial)
		require(partial["data"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) == nil, partial)
	}
	fmt.Println("PASS binding and body failures reach the expected effects and leave the tail absent and data unfrozen")
}

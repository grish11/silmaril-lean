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
def factory(value):
    def child(first, *rest, key=value, **extras):
        marked = [44]
        print(marked[0])
        probe = key[0]
        seen = value[0]
        print(probe, seen)
        return late
    copy = child
    value = [52]
    return copy
escaped = factory(data)
late = [83]
alias = escaped
result = alias(another=[61], *[data, data], **%s)
after = [99]
`, mapping)
}

func main() {
	opts := &syntax.FileOptions{}
	var events []string
	thread := &starlark.Thread{Print: func(_ *starlark.Thread, msg string) { events = append(events, msg) }}
	published, err := starlark.ExecFileOptions(opts, thread, "escaped.star", source(`{"extra": late}`), nil)
	require(err == nil, err)
	require(published["escaped"] == published["alias"] && published["result"] == published["late"], published)
	require(published["after"].String() == "[99]" && strings.Join(events, ",") == "44,31 52", events)
	for _, name := range []string{"data", "late"} {
		require(published[name].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, name)
	}
	fmt.Println("PASS escaped alias uses the saved default, live local and defining global, then publishes frozen values")

	events = nil
	_, program, err := starlark.SourceProgramOptions(opts, "escaped-error.star", source(`{"key": 8}`),
		func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(thread, nil)
	require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
	require(partial["escaped"] != nil && partial["escaped"] == partial["alias"] &&
		partial["result"] == nil && partial["after"] == nil && strings.Join(events, ",") == "44", partial)
	for _, name := range []string{"data", "late"} {
		require(partial[name].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) == nil, name)
	}
	fmt.Println("PASS escaped call failure retains earlier effects, leaves the result and tail absent, and skips freezing")
}

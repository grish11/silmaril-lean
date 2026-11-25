// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func main() {
	provider, err := starlark.ExecFileOptions(&syntax.FileOptions{},
		&starlark.Thread{Name: "provider"}, "a.star", `def read():
    return x
x = 7
_secret = []
def bump():
    _secret.append(1)
`, nil)
	require(err == nil, fmt.Sprint(err))
	load := func(_ *starlark.Thread, name string) (starlark.StringDict, error) {
		if name != "provider" {
			return nil, fmt.Errorf("unavailable module %s", name)
		}
		return provider, nil
	}
	initConsumer := func(src string) (starlark.StringDict, error) {
		return starlark.ExecFileOptions(&syntax.FileOptions{},
			&starlark.Thread{Name: "consumer", Load: load}, "b.star", src+"\n", nil)
	}

	result, err := initConsumer(`load("provider", get="read")
x = 99
out = get()`)
	require(err == nil && result["out"].String() == "7" && result["get"] == nil,
		"imported closure must keep its defining module, and load aliases are file-local")
	_, err = initConsumer(`load("provider", "bump")
bump()`)
	require(err != nil && strings.Contains(err.Error(), "frozen list"), fmt.Sprint(err))
	fmt.Println("PASS module publication freezes private globals and imports preserve closure globals")

	_, err = initConsumer(`load("provider", "_secret")`)
	require(err != nil && strings.Contains(err.Error(), "not exported"), fmt.Sprint(err))
	_, err = initConsumer(`load("provider", x="read")
x = 2`)
	require(err != nil && strings.Contains(err.Error(), "x"), fmt.Sprint(err))
	_, err = initConsumer(`load("provider", "unknown")`)
	require(err != nil && strings.Contains(err.Error(), "not found"), fmt.Sprint(err))
	_, err = initConsumer(`load("missing", "read")`)
	require(err != nil && strings.Contains(err.Error(), "unavailable module"), fmt.Sprint(err))
	fmt.Println("PASS private import, name collision, absent export, and host module failures")
}

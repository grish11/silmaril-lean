// Run from the pinned Starlark-Go checkout with go run and this file's path.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const producer = `data = [31]
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
result = alias(another=[61], *[data, data], **{"extra": late})
after = [99]
`

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func checkConsumer(warm bool, consumer string) (partial, cached starlark.StringDict, events []string, err error) {
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	thread.Print = func(_ *starlark.Thread, msg string) {
		events = append(events, msg)
	}
	var initializations, hits int
	thread.Load = func(_ *starlark.Thread, module string) (starlark.StringDict, error) {
		require(module == "prodé.star", module)
		if cached != nil {
			hits++
			return cached, nil
		}
		initializations++
		globals, err := starlark.ExecFileOptions(opts, thread, module, producer, nil)
		if err == nil {
			cached = globals
		}
		return globals, err
	}
	if warm {
		_, err := thread.Load(thread, "prodé.star")
		require(err == nil, err)
	}
	_, program, err := starlark.SourceProgramOptions(opts, "consumer.star", consumer, func(string) bool { return false })
	require(err == nil, err)
	partial, err = program.Init(thread, nil)
	require(initializations == 1 && (hits == 1) == warm, []int{initializations, hits})
	return partial, cached, events, err
}

func check(warm bool, name, mapping string) {
	consumer := fmt.Sprintf(`load("prodé.star", loaded=%q)
starter = loaded
made = starter([41])
held = made
marker = [88]
result = held(another=[71], *[17, 18], **%s)
late = [199]
`, name, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	if name == "absent" {
		require(err != nil && strings.Contains(err.Error(), "absent") && strings.Join(events, ",") == "44,31 52", err)
		require(partial["starter"] == nil && partial["made"] == nil &&
			partial["result"] == nil && partial["late"] == nil, partial)
	} else if mapping == `{"key": 8}` {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(strings.Join(events, ",") == "44,31 52,44" && partial["result"] == nil && partial["late"] == nil, partial)
		require(partial["starter"] == cached["factory"] && partial["made"] != nil && partial["made"] == partial["held"] &&
			partial["marker"].String() == "[88]", partial)
	} else {
		require(err == nil, err)
		partial.Freeze()
		require(partial["result"] == cached["late"] && partial["late"].String() == "[199]" &&
			partial["loaded"] == nil && strings.Join(events, ",") == "44,31 52,44,41 52", partial)
		require(partial["starter"] == cached["factory"] && partial["made"] == partial["held"] &&
			partial["made"] != cached["escaped"] && partial["marker"].String() == "[88]", partial)
		require(partial["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
	require(cached["data"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
	require(cached["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
}

func checkWrapper(warm bool, name, mapping string) {
	consumer := fmt.Sprintf(`load("prodé.star", loaded=%q)
def relay():
    return loaded(another=[71], *[17, 18], **%s)
result = relay()
`, name, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	switch {
	case name == "absent":
		require(err != nil && strings.Contains(err.Error(), "absent"), err)
		require(partial["relay"] == nil && partial["result"] == nil && strings.Join(events, ",") == "44,31 52", partial)
	case mapping == `{"key": 8}`:
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["relay"] != nil && partial["result"] == nil && strings.Join(events, ",") == "44,31 52,44", partial)
	default:
		require(err == nil, err)
		partial.Freeze()
		require(partial["relay"] != nil && partial["loaded"] == nil && partial["result"] == cached["late"] &&
			strings.Join(events, ",") == "44,31 52,44,31 52", partial)
		require(partial["result"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkDeclarationSuite(warm, bad bool) {
	mapping := `{"key": [72]}`
	if bad {
		mapping = `{"key": 8}`
	}
	consumer := fmt.Sprintf(`load("prodé.star", loaded="escaped")
def first():
    return loaded(another=[71], *[17, 18], **{"extra": 9})
copied = first
marker = [88]
def second():
    return loaded(another=[71], *[17, 18], **%s)
firstOut = copied()
secondOut = second()
after = [199]
`, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	require(partial["first"] != nil && partial["copied"] == partial["first"] &&
		partial["second"] != nil && partial["second"] != partial["first"], partial)
	require(partial["firstOut"] == cached["late"] && partial["marker"].String() == "[88]", partial)
	if bad {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["secondOut"] == nil && partial["after"] == nil &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44", partial)
	} else {
		require(err == nil, err)
		partial.Freeze()
		require(partial["secondOut"] == cached["late"] && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,72 52", partial)
		require(partial["firstOut"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkReturnedClosure(warm bool) {
	consumer := `load("prodé.star", loaded="factory")
def make():
    return loaded([41])
held = make()
result = held(17)
`
	partial, cached, events, err := checkConsumer(warm, consumer)
	require(err == nil, err)
	require(partial["held"] != nil && partial["held"] != cached["escaped"] &&
		partial["result"] == cached["late"] && strings.Join(events, ",") == "44,31 52,44,41 52", partial)
}

func checkChain(preload string, bad bool) {
	const middle = `load("prodé.star", loaded="escaped")
def relay():
    return loaded(17)
before = relay()
reexport = loaded
`
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	var events []string
	thread.Print = func(_ *starlark.Thread, message string) {
		events = append(events, message)
	}
	files := map[string]string{"prodé.star": producer, "middle.star": middle}
	cache := map[string]starlark.StringDict{}
	initializations := map[string]int{}
	hits := map[string]int{}
	thread.Load = func(_ *starlark.Thread, name string) (starlark.StringDict, error) {
		if value, found := cache[name]; found {
			hits[name]++
			return value, nil
		}
		source, exists := files[name]
		require(exists, name)
		initializations[name]++
		value, err := starlark.ExecFileOptions(opts, thread, name, source, nil)
		if err == nil {
			cache[name] = value
		}
		return value, err
	}
	if preload != "" {
		_, err := thread.Load(thread, preload)
		require(err == nil, err)
	}
	mapping := `{"key": [72]}`
	if bad {
		mapping = `{"key": 8}`
	}
	source := fmt.Sprintf(`load("middle.star", transferred="reexport")
held = transferred
first = held(another=[71], *[17, 18])
marker = [88]
answer = held(another=[71], *[17, 18], **%s)
after = [199]
`, mapping)
	_, program, err := starlark.SourceProgramOptions(opts, "final.star", source, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(thread, nil)
	require(initializations["prodé.star"] == 1 && initializations["middle.star"] == 1, initializations)
	require((hits["prodé.star"] == 1) == (preload == "prodé.star") &&
		(hits["middle.star"] == 1) == (preload == "middle.star"), hits)
	prod, mid := cache["prodé.star"], cache["middle.star"]
	require(mid["relay"] != nil && mid["reexport"] == prod["escaped"] &&
		partial["held"] == prod["escaped"] && mid["before"] == prod["late"] &&
		partial["first"] == prod["late"] && partial["marker"].String() == "[88]", partial)
	if bad {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["answer"] == nil && partial["after"] == nil &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,31 52,44", partial)
	} else {
		require(err == nil, err)
		require(partial["answer"] == prod["late"] && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,31 52,44,72 52", partial)
		require(partial["answer"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
	// A later request imports the middle wrapper itself. This control
	// observes resolved loading beyond the regular re-export theorem.
	wrapped, err := starlark.ExecFileOptions(opts, thread, "wrapped.star", `load("middle.star", wrapped="relay")
result = wrapped()
`, nil)
	require(err == nil, err)
	require(wrapped["result"] == prod["late"] && initializations["middle.star"] == 1, wrapped)
}

func main() {
	for _, warm := range []bool{false, true} {
		check(warm, "factory", `{"extra": 9}`)
		check(warm, "factory", `{"key": 8}`)
		check(warm, "absent", `{"extra": 9}`)
		checkWrapper(warm, "escaped", `{"extra": 9}`)
		checkWrapper(warm, "escaped", `{"key": 8}`)
		checkWrapper(warm, "absent", `{"extra": 9}`)
		checkDeclarationSuite(warm, false)
		checkDeclarationSuite(warm, true)
		checkReturnedClosure(warm)
	}
	for _, preload := range []string{"", "prodé.star", "middle.star"} {
		checkChain(preload, false)
		checkChain(preload, true)
	}
	fmt.Println("PASS cold and cached importer suites retain callable returns, saved values and producer globals")
	fmt.Println("PASS missing export stops the suite and a second-call error retains the factory and marker")
	fmt.Println("PASS consumer-owned wrapper calls the imported closure on cold and cached loads; reached errors preserve prior effects")
	fmt.Println("PASS interleaved importer declarations, alias calls, saved defaults, and skipped effects after the first error")
	fmt.Println("PASS a consumer wrapper returns a fresh imported closure that remains callable")
	fmt.Println("PASS three-module re-export with cold, root-preloaded and middle-preloaded histories")
}

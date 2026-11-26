package main

import (
	"fmt"

	"go.starlark.net/syntax"
)

// These Go-only controls use mutation to record evaluation order. The shared
// text fixtures compare nested spread results and competing errors.
func checkGoSpreadControls() (int, error) {
	const setup = `events = []
def mark(tag, value):
    events.append(tag)
    return value
def choose(callable, marker, required):
    return callable
def f(a, b, c, d):
    events.append(5)
    return d
xs = [2]
kw = {"d": 7}
duplicate = {"c": 7}
wrong = 0
`
	cases := []struct {
		name    string
		call    string
		control moduleControl
	}{
		{"callee-and-operand-effects", "mark(0, f)(mark(1, 1), c=mark(2, 3), *mark(3, xs), **mark(4, kw))",
			moduleControl{Phase: "publication", Want: "7", Events: "[0, 1, 2, 3, 4, 5]"}},
		{"callee-effects-before-callee-error", "choose(f, mark(0, 0))(mark(1, 1), c=mark(2, 3), *mark(3, xs), **mark(4, kw))",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[0]"}},
		{"middle-application-masks-later-effects", "mark(1, choose)(f, mark(2, 0))(mark(3, 0))(mark(4, 0))",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1, 2]"}},
		{"operand-effects", "f(mark(1, 1), c=mark(2, 3), *mark(3, xs), **mark(4, kw))",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2, 3, 4, 5]"}},
		{"effects-before-spread-error", "f(mark(1, 1), c=mark(2, 3), *mark(3, wrong), **mark(4, kw))",
			moduleControl{Phase: "runtime", Want: "argument after * must be iterable", Events: "[1, 2, 3, 4]"}},
		{"effects-before-binding-error", "f(mark(1, 1), c=mark(2, 3), *mark(3, xs), **mark(4, duplicate))",
			moduleControl{Phase: "runtime", Want: `multiple values for parameter "c"`, Events: "[1, 2, 3, 4]"}},
		{"named-after-star", "f(1, *xs, c=3, **kw)",
			moduleControl{Phase: "validation", Want: "keyword argument may not follow *args"}},
		{"star-after-mapping", "f(1, c=3, **kw, *xs)",
			moduleControl{Phase: "validation", Want: "*args may not follow **kwargs"}},
	}
	for _, test := range cases {
		file, err := (&syntax.FileOptions{}).Parse(test.name+".star", setup+"out = "+test.call, 0)
		if err != nil {
			return 0, fmt.Errorf("%s: %w", test.name, err)
		}
		if err := checkModule(file, test.control); err != nil {
			return 0, fmt.Errorf("%s: %w", test.name, err)
		}
	}
	return len(cases), nil
}

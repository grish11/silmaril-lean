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
def assign_fail():
    saved = choose(f, mark(1, 0))
    later = mark(2, 99)
    return later
def eval_ok():
    if True:
        mark(1, 0); mark(2, 0)
    return 7
def eval_fail():
    choose(f, mark(1, 0)); mark(2, 0)
    return 7
def branch_first():
    if mark(1, True) or mark(90, False):
        return mark(2, 7)
    elif mark(91, True):
        mark(92, 0)
    return mark(93, 0)
def branch_elif():
    if mark(1, False):
        mark(90, 0)
    elif mark(3, True) if mark(2, True) else mark(91, False):
        return mark(4, 7)
    elif mark(92, True):
        mark(93, 0)
    return mark(94, 0)
def branch_fail():
    if mark(1, False):
        mark(90, 0)
    elif choose(f, mark(2, 0)):
        mark(91, 0)
    elif mark(92, True):
        mark(93, 0)
    else:
        mark(94, 0)
    return mark(95, 0)
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
		{"failed-body-assignment-masks-later-effects", "assign_fail()",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1]"}},
		{"call-statement-effects", "eval_ok(); mark(3, 0); mark(4, 0)",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2, 3, 4]"}},
		{"failed-call-statement-masks-later-effects", "eval_fail()",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1]"}},
		{"logical-call-effects", "mark(1, 1) and mark(2, 7) or mark(3, 99)",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2]"}},
		{"logical-call-error-masks-later-effects", "choose(f, mark(1, 0)) and mark(2, 0) or mark(3, 0)",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1]"}},
		{"conditional-then-effects", "mark(2, 7) if mark(1, True) else mark(3, 99)",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2]"}},
		{"conditional-condition-error-masks-arm-effects", "mark(2, 7) if choose(f, mark(1, 0)) else mark(3, 99)",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1]"}},
		{"conditional-selected-error-masks-other-arm-effects", "mark(3, 99) if mark(1, False) else choose(f, mark(2, 0))",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1, 2]"}},
		{"if-effects-skip-short-circuit-and-later-elifs", "branch_first()",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2]"}},
		{"elif-condition-effects-before-suite", "branch_elif()",
			moduleControl{Phase: "publication", Want: "7", Events: "[1, 2, 3, 4]"}},
		{"elif-error-retains-effects-and-masks-later-tests", "branch_fail()",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1, 2]"}},
		{"list-elements-run-in-order-and-skip-conditional-arm",
			"len([mark(1, 7), [mark(3, 8) if mark(2, True) else mark(90, 0),], mark(4, 9),])",
			moduleControl{Phase: "publication", Want: "3", Events: "[1, 2, 3, 4]"}},
		{"list-failure-keeps-prefix-and-masks-later-element",
			"len([[mark(1, 7)], choose(f, mark(2, 0)), mark(90, 0)])",
			moduleControl{Phase: "runtime", Want: "missing 1 argument (required)", Events: "[1, 2]"}},
		{"tuple-elements-run-in-order-and-skip-conditional-arm",
			"len((mark(1, 7), (mark(3, 8) if mark(2, True) else mark(90, 0),), mark(4, 9),))",
			moduleControl{Phase: "publication", Want: "3", Events: "[1, 2, 3, 4]"}},
		{"tuple-failure-keeps-prefix-and-masks-later-element",
			"len(((mark(1, 7),), choose(f, mark(2, 0)), mark(90, 0)))",
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

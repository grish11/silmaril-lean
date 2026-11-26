// Run from the pinned starlark-go checkout. The fixtures arrive from Lean.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

type fixture struct {
	Name    string
	Source  string
	Accepts bool
	Module  *moduleControl
	Loader  *loaderControl
}

type moduleControl struct {
	Phase  string
	Want   string
	Events string
}

type loaderControl struct {
	Phase    string
	Want     string
	Label    string
	Producer string
	Marker   string
	Wrapper  string
}

func isInteger(value starlark.Value, want string) bool {
	integer, ok := value.(starlark.Int)
	return ok && integer.String() == want
}

func checkModule(file *syntax.File, control moduleControl) error {
	program, err := starlark.FileProgram(file, func(string) bool { return false })
	if control.Phase == "validation" {
		if err != nil && strings.Contains(err.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want validation error containing %q, got %v", control.Want, err)
	}
	if err != nil {
		return fmt.Errorf("unexpected validation error: %w", err)
	}

	globals, err := program.Init(new(starlark.Thread), nil)
	if control.Events != "" {
		events, ok := globals["events"].(*starlark.List)
		if !ok || events.String() != control.Events {
			return fmt.Errorf("want events %s, got %v", control.Events, globals["events"])
		}
	}
	if control.Phase == "runtime" {
		if err != nil && strings.Contains(err.Error(), control.Want) && globals["out"] == nil {
			return nil
		}
		return fmt.Errorf("want runtime error containing %q with out unbound, got error %v and out %v",
			control.Want, err, globals["out"])
	}
	if control.Phase != "publication" {
		return fmt.Errorf("unknown module phase %q", control.Phase)
	}
	if err != nil {
		return fmt.Errorf("unexpected runtime error: %w", err)
	}
	globals.Freeze()
	if !isInteger(globals["out"], control.Want) {
		return fmt.Errorf("want out to be integer %s, got %v", control.Want, globals["out"])
	}
	return nil
}

func checkLoader(file *syntax.File, parseError error, control loaderControl) error {
	if control.Phase == "parse" {
		if parseError != nil && strings.Contains(parseError.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want parse error containing %q, got %v", control.Want, parseError)
	}
	if parseError != nil {
		return fmt.Errorf("unexpected parse error: %w", parseError)
	}

	program, err := starlark.FileProgram(file, func(string) bool { return false })
	if control.Phase == "validation" {
		if err != nil && strings.Contains(err.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want validation error containing %q, got %v", control.Want, err)
	}
	if err != nil {
		return fmt.Errorf("unexpected validation error: %w", err)
	}

	var requested []string
	thread := &starlark.Thread{Load: func(_ *starlark.Thread, label string) (starlark.StringDict, error) {
		requested = append(requested, label)
		if label != control.Label {
			return nil, fmt.Errorf("unexpected label %q", label)
		}
		return starlark.ExecFileOptions(&syntax.FileOptions{}, new(starlark.Thread),
			"producer.star", []byte(control.Producer), nil)
	}}
	globals, err := program.Init(thread, nil)
	if len(requested) != 1 || requested[0] != control.Label {
		return fmt.Errorf("want one request for %q, got %v", control.Label, requested)
	}
	if control.Phase == "runtime" {
		marker := globals["marker"]
		markerMatches := marker == nil && control.Marker == "" || isInteger(marker, control.Marker)
		if err != nil && strings.Contains(err.Error(), control.Want) && globals["out"] == nil && markerMatches {
			return nil
		}
		return fmt.Errorf("want error containing %q with out unbound and marker %q, got %v and %v",
			control.Want, control.Marker, err, globals)
	}
	if control.Phase != "publication" {
		return fmt.Errorf("unknown loader phase %q", control.Phase)
	}
	if err != nil {
		return fmt.Errorf("unexpected runtime error: %w", err)
	}
	globals.Freeze()
	wantCount := 1
	if control.Wrapper != "" {
		wantCount++
		if _, ok := globals[control.Wrapper].(*starlark.Function); !ok {
			return fmt.Errorf("want wrapper function %s, got %v", control.Wrapper, globals)
		}
	}
	if len(globals) != wantCount || !isInteger(globals["out"], control.Want) {
		return fmt.Errorf("want out = %s among %d globals, got %v", control.Want, wantCount, globals)
	}
	return nil
}

func main() {
	var fixtures []fixture
	if err := json.NewDecoder(os.Stdin).Decode(&fixtures); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if len(fixtures) == 0 {
		fmt.Fprintln(os.Stderr, "no Starlark frontend fixtures")
		os.Exit(1)
	}
	failed := false
	modules := 0
	loaders := 0
	for _, f := range fixtures {
		file, err := (&syntax.FileOptions{}).Parse(f.Name+".star", []byte(f.Source), 0)
		if (err == nil) != f.Accepts {
			fmt.Fprintf(os.Stderr, "%s: want Go acceptance %t, got %v\n", f.Name, f.Accepts, err)
			failed = true
			continue
		}
		if f.Module != nil {
			modules++
			if err != nil {
				fmt.Fprintf(os.Stderr, "%s: module control needs a Go syntax tree: %v\n", f.Name, err)
				failed = true
				continue
			}
			if err := checkModule(file, *f.Module); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.Loader != nil {
			loaders++
			if err := checkLoader(file, err, *f.Loader); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
	}
	spreads, err := checkGoSpreadControls()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		failed = true
	}
	if failed {
		os.Exit(1)
	}
	fmt.Printf("Pinned Go matched %d parse expectations, %d module observations, %d loader controls, and %d Go-only spread controls\n",
		len(fixtures), modules, loaders, spreads)
}

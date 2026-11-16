module

public import Silmaril.Project.Core.Defs
public import Silmaril.Semantics.Accept.Regex.Defs
public import Silmaril.Semantics.Accept.MonoidRegex.Defs
public import Mathlib.Data.Fin.VecNotation

/-!
# Languages of a silmaril project: the constructors

A **language** over a domain `α` is a set `Set α` (for byte strings, `Set (List UInt8)`, which
is Mathlib's `Language UInt8` and silmaril's `Formats.Accept.ByteLang`). The registry
(`Silmaril.Project.Registry.Language.Defs`) names languages and records how each one was
built; every constructor it offers is one of the definitions below, or a Lean definition the
project supplies, or a set operation (`∪`, `∩`, `\`), or the evaluation of a regular
expression (`Silmaril.Accept.Regex.Expr.eval` for list domains,
`Silmaril.Accept.MonoidRegex.Expr.eval` for other monoids).

* `formatLang F`: the byte strings a project format `F : Format blob V` parses. The value
  produced is forgotten; only success matters.
* `artifactLang X I`: the language an **interpreted artifact** denotes. `X` is a project value
  (bytes pinned by content identifier, read under a format into `V`, for example a Wasm module
  or component), and `I : V → Set α` is an explicit interpretation: which execution
  semantics, ABI decoding and admitted environments make the artifact an acceptor. The
  language is `I v` for the value `v` the bytes parse to, and empty if they do not parse. The
  artifact's hash alone does not determine the language; the interpretation is part of it.
* `within L μ b`: the members of `L` whose measure `μ x` is at most `b`
  (`Silmaril.Accept.within`, restricted to `L`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Project.Languages

universe u

/-- **The byte language of a project format**: the byte strings it parses. -/
def formatLang {V : Type} (F : Format blob V) : Set (List UInt8) :=
  {w | (F.parse (Silmaril.Formats.Bytes.ofList w)).isSome = true}

/-- **The language of an interpreted artifact**: `I v` for the value `v` that the bytes of `X`
parse to (empty when they do not parse). -/
def artifactLang {V : Type} {α : Type u} (X : Value V) (I : V → Set α) : Set α :=
  {a | ∃ v, X.parse = some v ∧ a ∈ I v}

/-- **A measure-restricted language**: the members of `L` with `μ x ≤ b`. -/
def within {α : Type u} (L : Set α) (μ : α → ℕ) (b : ℕ) : Set α := {x | x ∈ L ∧ μ x ≤ b}

end Silmaril.Project.Languages

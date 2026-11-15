module

public import Silmaril.Semantics.Accept.Rel.Defs

/-!
# Successful-value projections of status-carrying relations

Many programs answer with a value that carries its own status: an `Option β` (`none` = no
value), an `Except ε β` (`.error e` = failure) or a sum `β ⊕ ε` (in this repository WIT
`result<T, E>` is interpreted as `T ⊕ E` with `inl` = `ok`, see
`Silmaril/Wasm/Component/Reference/WIT/Interp/Defs.lean`).
A relation `R : α -|> γ` into such a type is projected onto its *successful* values by a
partial function `f : γ → Option β` that extracts the success and fails otherwise:

* `succ f R := R ○ ofPartial f`: keep the outputs `c` of `R` with `f c = some b`, as `b`.
  Outputs with `f c = none` (a `none`, an `.error`, an `inr`) are dropped: an input whose only
  outputs are failures has no output in `succ f R` (`Thms`).

Extractors (all partial functions, so `succ` composes through `partialComp`):

| extractor | input | keeps |
| --- | --- | --- |
| `optionOk` | `Option β` | `some b` |
| `exceptOk` / `exceptErr` | `Except ε β` | `.ok b` / `.error e` |
| `sumOk` / `sumErr` | `β ⊕ ε` | `inl b` / `inr e` |

`someVals`, `okVals`, `inlVals` (and the error sides `errVals`, `inrVals`) are `succ` along
these extractors.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w x

open scoped SetRel

variable {α : Type u} {β : Type v} {γ : Type w} {ε : Type x}

/-- The successful values of `R` along the extractor `f`: `(a, b)` when `R` relates `a` to
some `c` with `f c = some b`. -/
def succ (f : γ → Option β) (R : α -|> γ) : α -|> β := R ○ ofPartial f

/-- Extract the value of an `Option`: the identity, as an extractor. -/
def optionOk : Option β → Option β := id

/-- Extract the success value of an `Except`: `.ok b ↦ some b`, `.error _ ↦ none`. -/
def exceptOk : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

/-- Extract the error of an `Except`: `.error e ↦ some e`, `.ok _ ↦ none`. -/
def exceptErr : Except ε β → Option ε
  | .ok _ => none
  | .error e => some e

/-- Extract the success value of a sum, `inl` being success (WIT `result` decodes `ok` to
`Sum.inl`). -/
def sumOk : β ⊕ ε → Option β
  | .inl b => some b
  | .inr _ => none

/-- Extract the error of a sum: `inr e ↦ some e`. -/
def sumErr : β ⊕ ε → Option ε
  | .inl _ => none
  | .inr e => some e

/-- The `some` values of an `Option`-valued relation. -/
abbrev someVals (R : α -|> Option β) : α -|> β := succ optionOk R

/-- The `.ok` values of an `Except`-valued relation. -/
abbrev okVals (R : α -|> Except ε β) : α -|> β := succ exceptOk R

/-- The `.error` values of an `Except`-valued relation. -/
abbrev errVals (R : α -|> Except ε β) : α -|> ε := succ exceptErr R

/-- The `inl` (success) values of a sum-valued relation. -/
abbrev inlVals (R : α -|> β ⊕ ε) : α -|> β := succ sumOk R

/-- The `inr` (error) values of a sum-valued relation. -/
abbrev inrVals (R : α -|> β ⊕ ε) : α -|> ε := succ sumErr R

end Silmaril.Accept

module

public import Silmaril.Logic.Consequence.Interp.Defs
public import Silmaril.Logic.Consequence.Gentzen.Thms
public import Silmaril.Logic.Consequence.Multi.Defs

/-!
# Gentzen operations on interpretations

Core `Interp Env Value Ax C` reads a value as an optional consequence system
(`Silmaril.Logic.Consequence.Interp`). For a formula family `F : Env → Type`, an interpretation
of values as Gentzen sequent relations is `GInterp Env Value F` (contexts and conclusions are
lists of `F e`). The operations here are instances of core `Interp.map`:

* `GInterp.closure rs I`: close every defined reading under the rules `rs e`;
* `GInterp.single I`: the single-conclusion restriction (core `MultiSystem.single`).

Undefined readings stay undefined: closing does not commute with core `orBot` (which reads an
undefined value as `⊥`), because the closure of `⊥` under reflexivity is not `⊥`
(`…Gentzen.Interp.Thms`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen

universe u v w

/-- Interpretations of values as Gentzen sequent relations over `F e`. -/
abbrev GInterp (Env : Type u) (Value : Type v) (F : Env → Type w) : Type (max u v w) :=
  Interp Env Value (fun e => List (F e)) (fun e => List (F e))

namespace GInterp

variable {Env : Type u} {Value : Type v} {F : Env → Type w}

/-- Close every defined reading under the rules `rs e`. -/
def closure (rs : (e : Env) → Rules (F e)) (I : GInterp Env Value F) : GInterp Env Value F :=
  I.map fun e S => Derives (rs e) S

/-- The single-conclusion restriction of every defined reading. -/
def single (I : GInterp Env Value F) : Interp Env Value (fun e => List (F e)) F :=
  I.map fun _ S => MultiSystem.single S

end GInterp

end Silmaril.Consequence.Gentzen

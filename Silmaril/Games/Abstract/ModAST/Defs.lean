module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Module ASTs parameterised by the function representation

The analysis factory reads bytes into a module, the module into functions in
some representation (code, a basic-block CFG, an instruction-level CFG, an
abstract function), and lifts equivalences and refinements from functions to
modules. This module gives the generic module layer for that lift.

* `ModAST sh R`: a module of internal shape `sh` whose functions are in
  representation `R`. The shape is fixed: the same functions, types and
  internal state for every representation.
* `ModAST.map g`: change the representation function by function, preserving
  the shape (a shape-preserving projection).
* `FunSem sh R`: a semantics of the representation, each function read as an
  open abstract function (`Silmaril.Games.Abstract.Shape.OpenMod`) that may call
  imports and the module's own functions.
* `ModAST.den m` is the open module, and `ModAST.closed m` its closure by the
  least fixpoint (`Shape.close`).

`Silmaril.Games.Abstract.ModAST.Thms` proves the compositional facts:

* a representation change that commutes with the semantics function by
  function does not change the module semantics;
* function-wise trap ≈ divergence equivalence gives module equivalence;
* function-wise refinement gives module refinement.

Each follows from congruence of closing, not from recomputing the module.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u v w

/-- A module of shape `sh` with functions in representation `R`. -/
abbrev ModAST (sh : Shape.{u}) (R : Type v) : Type (max u v) := sh.F → R

/-- A semantics of a function representation: each function as an open
abstract function of the module. -/
class FunSem (sh : Shape.{u}) (R : Type v) where
  /-- The open abstract function of the representation of `f`. -/
  den : (f : sh.F) → R → AFun (sh.E ⊕ₛ sh.self) sh.S (sh.A f) (sh.B f)

namespace ModAST

variable {sh : Shape.{u}} {R : Type v} {R' : Type w}

/-- Change the representation, function by function. -/
def map (g : R → R') (m : ModAST sh R) : ModAST sh R' := fun f => g (m f)

/-- The open module of a module AST. -/
def den [FunSem sh R] (m : ModAST sh R) : sh.OpenMod := fun f => FunSem.den f (m f)

/-- The closed module (least fixpoint of internal calls). -/
def closed [FunSem sh R] (m : ModAST sh R) : sh.ClosedMod := Shape.close m.den

end ModAST

end Silmaril.Games.Abstract

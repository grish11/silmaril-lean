module

public import Silmaril.Games.Abstract.ModAST.Defs
public import Silmaril.Games.Abstract.Module.Thms

/-!
# Module ASTs parameterised by the function representation: theorems

* `den_map`: if a change of representation `g` commutes with the semantics
  function by function, the module semantics is unchanged. This is the
  obligation a representation change (instruction-level against block-level
  CFG, kernel AST against runtime AST) must discharge once per function.
* `closed_congr`, `closedD_congr`, `closeInf_congr`: if two module ASTs are
  trap ≈ divergence equivalent function by function, their closed modules are
  equivalent: least fixpoint, with divergence chains, and their infinite
  runs. This is compositional congruence (`Shape.close_congr`), not
  recomputation. In particular, replacing one function by an equivalent one
  gives an equivalent module.
* `closed_mono`: function-wise refinement (inclusion of behaviours) gives
  module refinement.

All three use the open semantics of each function. Whether a concrete
representation's `FunSem` agrees with Core 3.0 execution is a separate
obligation of that representation; for internal calls it is the open
internal-call bridge.
-/

public section

namespace Silmaril.Games.Abstract.ModAST

universe u v w

variable {sh : Shape.{u}} {R : Type v} {R' : Type w} [FunSem sh R] [FunSem sh R']

/-- A semantics-commuting representation change preserves the module semantics. -/
theorem den_map (g : R → R') (hg : ∀ f r, FunSem.den (sh := sh) f (g r) = FunSem.den f r)
    (m : ModAST sh R) : (m.map g).den = m.den :=
  funext fun f => hg f (m f)

/-- Function-wise trap ≈ divergence equivalence gives module equivalence. -/
theorem closed_congr {m : ModAST sh R} {m' : ModAST sh R'}
    (h : ∀ f, AFun.ObsEquiv AFun.obsCollapse (FunSem.den f (m f)) (FunSem.den f (m' f))) :
    Shape.ClosedCollapseEquiv m.closed m'.closed :=
  Shape.close_congr h

/-- The same for closing with divergence chains. -/
theorem closedD_congr {m : ModAST sh R} {m' : ModAST sh R'}
    (h : ∀ f, AFun.ObsEquiv AFun.obsCollapse (FunSem.den f (m f)) (FunSem.den f (m' f))) :
    Shape.ClosedCollapseEquiv (Shape.closeD m.den) (Shape.closeD m'.den) :=
  Shape.closeD_congr h

/-- The same for infinite runs through recursion. -/
theorem closeInf_congr {m : ModAST sh R} {m' : ModAST sh R'}
    (h : ∀ f, AFun.ObsEquiv AFun.obsCollapse (FunSem.den f (m f)) (FunSem.den f (m' f)))
    (f : sh.F) (s : sh.S) (a : sh.A f) :
    Shape.closeInf m.den f s a = Shape.closeInf m'.den f s a :=
  Shape.closeInf_congr h f s a

/-- Function-wise refinement gives module refinement. -/
theorem closed_mono {m : ModAST sh R} {m' : ModAST sh R'}
    (h : ∀ f, FunSem.den f (m f) ≤ FunSem.den f (m' f)) : m.closed ≤ m'.closed :=
  Shape.close_mono h

end Silmaril.Games.Abstract.ModAST

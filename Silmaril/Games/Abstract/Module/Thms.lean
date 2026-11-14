module

public import Silmaril.Games.Abstract.Module.Defs
import Silmaril.Proofs.Games.Abstract.Module.Basic
import Silmaril.Proofs.Games.Abstract.Module.Congruence
import Silmaril.Proofs.Games.Abstract.Module.Infinite

/-!
# Abstract modules: theorems

* `close_mono`: closing is monotone in the open module.
* `resolve_close`: the closed module is a fixpoint of resolution, so each
  closed function's behaviours are its open behaviours with internal calls
  answered by closed behaviours.
* `close_lift`: a module with no internal calls closes to itself. Concrete
  modules whose internal calls are already resolved (Core 3.0 under its store
  semantics) are of this kind.
* `sup_close_le` and `exists_close_not_sup`: the join of closed modules is
  below the closure of the join, and strictly below in general. If one module
  provides `g` and another a function `f` that calls `g`, their join closes to
  an `f` that returns, while neither closes to one. Joins of modules of a
  fixed shape must therefore be taken on open modules and then closed. The
  pointwise join of closed modules is not the closure of anything that links.

**Least fixpoint against divergence (audit).** `close` keeps only finite
derivations. A callee's `div` propagates, but an unproductive recursion is
not detected:

* `exists_close_omits_div`: `f` calling itself closes to the empty set, so
  it has no `div` behaviour.
* `closeD` adds `div` after the import calls of every infinite internal-call
  chain with finitely many import calls. It observes that recursion
  (`exists_closeD_observes_rec_div`), extends `close` (`close_le_closeD`),
  and agrees with it when there are no internal calls (`closeD_lift`).
* Chains with infinitely many import calls are infinite productive runs.
  `closeInf` collects their import-call streams.
  `exists_rec_import_inf`: `f () = e (); f ()` has no finite behaviour and no
  divergence, but one infinite run `e (), e (), …`. There are none without
  internal calls (`closeInf_lift`) or with a well-founded call graph
  (`closeInf_empty_of_wf`), and trap ≈ divergence equivalent open modules
  have the same ones (`closeInf_congr`).
* Still not represented: infinite runs *inside* one open function with no
  internal call, because `AFun` has no infinite behaviours.

`closeD_eq_close_of_wf`: when the internal calls follow a well-founded call
graph (`RespectsCalls`), for example an acyclic static call graph over finitely
many functions, `closeD = close`, so recursion cannot be a source of
divergence.

**Congruence.** `close_congr` and `closeD_congr`: open modules that are
equivalent up to trap ≈ divergence, function by function, close (with or
without divergence chains) to modules that are equivalent up to trap ≈
divergence. Equality (the tagged notion) is trivially preserved.

No theorem yet says that `closeD` agrees with an operational semantics with
recursion. Agreement with Core 3.0 recursion is the next milestone.
-/

public section

namespace Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-- Closing is monotone. -/
theorem close_mono {m m' : sh.OpenMod} (h : m ≤ m') : close m ≤ close m' :=
  Silmaril.Proofs.Games.Abstract.Module.close_mono h

/-- The closed module is a fixpoint of resolution. -/
theorem resolve_close (m : sh.OpenMod) : resolve m (close m) = close m :=
  Silmaril.Proofs.Games.Abstract.Module.resolve_close m

/-- A module with no internal calls closes to itself. -/
theorem close_lift (c : sh.ClosedMod) : close (lift c) = c :=
  Silmaril.Proofs.Games.Abstract.Module.close_lift c

/-- The join of closed modules is below the closure of the join. -/
theorem sup_close_le (m m' : sh.OpenMod) : close m ⊔ close m' ≤ close (m ⊔ m') :=
  Silmaril.Proofs.Games.Abstract.Module.sup_close_le m m'

open Silmaril.Proofs.Games.Abstract.Module in
/-- Closing does not commute with joins. -/
theorem exists_close_not_sup :
    ∃ (sh : Shape.{0}) (m m' : sh.OpenMod), close m ⊔ close m' ≠ close (m ⊔ m') :=
  ⟨sh₀, m₁, m₂, close_not_sup⟩

open Silmaril.Proofs.Games.Abstract.Module in
/-- The least fixpoint omits divergence by unbounded recursion: a function
calling itself closes to no behaviour at all. -/
theorem exists_close_omits_div :
    ∃ (sh : Shape.{0}) (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f),
      close m f s a = ∅ ∧ (∃ x ∈ m f s a, x.1 ≠ []) :=
  ⟨sh₀, m₃, true, ⟨⟩, ⟨⟩, by rw [close_m₃]; rfl, ⟨_, rfl, by simp⟩⟩

open Silmaril.Proofs.Games.Abstract.Module in
/-- Closing with divergence observes that recursion. -/
theorem exists_closeD_observes_rec_div :
    ∃ (sh : Shape.{0}) (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f),
      close m f s a = ∅ ∧ ([], End.div) ∈ closeD m f s a :=
  ⟨sh₀, m₃, true, ⟨⟩, ⟨⟩, by rw [close_m₃]; rfl, div_mem_closeD_m₃⟩

/-- Closing with divergence extends closing. -/
theorem close_le_closeD (m : sh.OpenMod) : close m ≤ closeD m :=
  Silmaril.Proofs.Games.Abstract.Module.close_le_closeD m

/-- Without internal calls, closing with divergence is the identity. -/
theorem closeD_lift (c : sh.ClosedMod) : closeD (lift c) = c :=
  Silmaril.Proofs.Games.Abstract.Module.closeD_lift c

/-- With a well-founded call graph (no infinite descending chain, so no
recursion), closing with divergence adds nothing: divergence can only come
from callees, not from recursion. -/
theorem closeD_eq_close_of_wf {R : sh.F → sh.F → Prop} (hR : WellFounded R) {m : sh.OpenMod}
    (hm : RespectsCalls R m) : closeD m = close m :=
  Silmaril.Proofs.Games.Abstract.Module.closeD_eq_close_of_wf hR hm

/-- A module without internal calls respects every call graph. -/
theorem respectsCalls_lift (R : sh.F → sh.F → Prop) (c : sh.ClosedMod) :
    RespectsCalls R (lift c) :=
  Silmaril.Proofs.Games.Abstract.Module.respectsCalls_lift R c

/-- Trap ≈ divergence is a congruence for closing. -/
theorem close_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') :
    ClosedCollapseEquiv (close m) (close m') :=
  Silmaril.Proofs.Games.Abstract.Module.close_congr h

/-- Trap ≈ divergence is a congruence for closing with divergence chains. -/
theorem closeD_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') :
    ClosedCollapseEquiv (closeD m) (closeD m') :=
  Silmaril.Proofs.Games.Abstract.Module.closeD_congr h

open Silmaril.Proofs.Games.Abstract.Module in
/-- Recursion through an import: no finite behaviour, no divergence, one
infinite productive run. -/
theorem exists_rec_import_inf :
    ∃ (sh : Shape.{0}) (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f)
      (ω : Nat → Call sh.E), close m f s a = ∅ ∧ closeD m f s a = ∅ ∧ ω ∈ closeInf m f s a :=
  ⟨shI, m₄, ⟨⟩, ⟨⟩, ⟨⟩, eStream, by rw [close_m₄]; rfl, closeD_m₄, eStream_mem⟩

/-- No infinite runs without internal calls. -/
theorem closeInf_lift (c : sh.ClosedMod) (f : sh.F) (s : sh.S) (a : sh.A f) :
    closeInf (lift c) f s a = ∅ :=
  Silmaril.Proofs.Games.Abstract.Module.closeInf_lift c f s a

/-- No infinite runs through recursion with a well-founded call graph. -/
theorem closeInf_empty_of_wf {R : sh.F → sh.F → Prop} (hR : WellFounded R) {m : sh.OpenMod}
    (hm : RespectsCalls R m) (f : sh.F) (s : sh.S) (a : sh.A f) : closeInf m f s a = ∅ :=
  Silmaril.Proofs.Games.Abstract.Module.closeInf_empty_of_wf hR hm f s a

/-- Trap ≈ divergence equivalent open modules have the same infinite runs. -/
theorem closeInf_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') (f : sh.F) (s : sh.S)
    (a : sh.A f) : closeInf m f s a = closeInf m' f s a :=
  Silmaril.Proofs.Games.Abstract.Module.closeInf_congr h f s a

end Silmaril.Games.Abstract.Shape

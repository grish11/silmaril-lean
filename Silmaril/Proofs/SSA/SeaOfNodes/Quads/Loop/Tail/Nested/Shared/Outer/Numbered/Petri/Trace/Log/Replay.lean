module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Thms
import Mathlib.Data.List.Chain

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Fire finished pending Finishes finishes_term_iff)
open Relation (ReflTransGen)

theorem reaches {M : Type} {step : M → M → Prop} (start : M) (marks : List M)
    (legal : List.IsChain step (start :: marks)) : ReflTransGen step start (marks.getLastD start) := by
  induction marks generalizing start with
  | nil => exact .refl
  | cons after remaining ih =>
    obtain ⟨fires, tail⟩ := List.isChain_cons_cons.mp legal
    rw [List.getLastD_cons]
    exact (ih after tail).head fires

private theorem lift_prefix {A B : Type} {r : A → A → Prop} {s : B → B → Prop}
    (f : A → B) (lift : ∀ {a b}, r a b → s (f a) (f b))
    (start : A) (body : List A) (after : B) (remaining : List B)
    (legal : List.IsChain r (start :: body)) (consume : s (f (body.getLastD start)) after)
    (tail : List.IsChain s (after :: remaining)) :
    List.IsChain s (f start :: body.map f ++ after :: remaining) := by
  induction body generalizing start with
  | nil => exact List.isChain_cons_cons.mpr ⟨consume, tail⟩
  | cons b rest ih =>
    obtain ⟨first, legal⟩ := List.isChain_cons_cons.mp legal
    rw [List.getLastD_cons] at consume
    exact List.isChain_cons_cons.mpr ⟨lift first, ih b legal consume⟩

private theorem lastD_of_slice {M : Type} (front tail : List M) (start next : M) :
    (front ++ next :: tail).getLastD start = tail.getLastD next := by
  induction front generalizing start with
  | nil => exact List.getLastD_cons
  | cons _ _ ih => rw [List.cons_append, List.getLastD_cons, ih]

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

private theorem lift_body (pre : PreMark p) (old : Bank (regs := regs) model)
    {a b : BodyMark p} (step : BodyFire p old a b) :
    RootFire p input (atBody p pre old a) (atBody p pre old b) :=
  (entryCut p).lift_tail_step semantics input PUnit.unit pre (.advance step)

private theorem legal_slice {pre : PreMark p} {old : Bank (regs := regs) model}
    {start : BodyMark p} {roots : List (RootMark p)} (slice : Slice p input pre old start roots)
    (tail : List.IsChain (RootFire p input) (slice.after :: slice.remaining)) :
    List.IsChain (RootFire p input) (atBody p pre old start :: roots) := by
  have linked := lift_prefix (atBody p pre old) (lift_body p input pre old) start slice.body
    slice.after slice.remaining slice.legal slice.consumes tail
  exact slice.split.symm ▸ linked

private theorem restart_at {pre : PreMark p} {old : Bank (regs := regs) model}
    {roots : List (RootMark p)} (slice : Slice p input pre old (pending semantics (thetaBody p)) roots)
    (again : feedback slice.packet = true) :
    slice.after = atBody p pre (nextBankOf slice.packet) (pending semantics (thetaBody p)) := by
  rw [slice.destination, again]
  rfl

private theorem last_of_slice {pre : PreMark p} {old : Bank (regs := regs) model}
    {start : BodyMark p} {roots : List (RootMark p)} (slice : Slice p input pre old start roots) :
    roots.getLastD (atBody p pre old start) = slice.remaining.getLastD slice.after :=
  (congrArg (fun marks => marks.getLastD (atBody p pre old start)) slice.split).trans
    (lastD_of_slice _ _ _ _)

theorem recovered_legal {pre : PreMark p} {old : Bank (regs := regs) model} {roots : List (RootMark p)}
    (r : Recovered p input pre old roots) :
    List.IsChain (RootFire p input) (atBody p pre old (pending semantics (thetaBody p)) :: roots) := by
  induction r with
  | stop slice _ _ _ empty _ _ =>
    apply legal_slice p input slice
    exact empty.symm ▸ List.IsChain.singleton _
  | again slice _ _ again _ ih =>
    exact legal_slice p input slice ((restart_at p input slice again).symm ▸ ih)

theorem recovered_result {pre : PreMark p} {old : Bank (regs := regs) model} {roots : List (RootMark p)}
    (r : Recovered p input pre old roots) :
    finished semantics (emitted p) input PUnit.unit
      (roots.getLastD (atBody p pre old (pending semantics (thetaBody p)))) = some (r.result p input) := by
  induction r with
  | stop slice _ _ _ empty _ returned =>
    rw [last_of_slice p input slice]
    exact empty.symm ▸ returned
  | again slice _ _ again _ ih =>
    rw [last_of_slice p input slice, restart_at p input slice again]
    exact ih

theorem complete_legal {roots : List (RootMark p)} (check : Complete p input roots) :
    List.IsChain (RootFire p input) (pending semantics (emitted p) :: roots) := by
  let start := atBody p check.started.pre (entryBank (src := src) (entry := entry) input)
    (pending semantics (thetaBody p))
  have before : List.IsChain (RootFire p input)
      ((pending semantics (emitted p) :: check.started.earlier) ++ [start]) := check.started.legal
  have after : List.IsChain (RootFire p input) ([start] ++ check.started.remaining) :=
    recovered_legal p input check.recovery
  have path := before.append_overlap after (List.cons_ne_nil _ _)
  rw [check.started.split]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using path

theorem complete_result {roots : List (RootMark p)} (check : Complete p input roots) :
    finished semantics (emitted p) input PUnit.unit (roots.getLastD (pending semantics (emitted p))) =
      some (check.result p input) := by
  have last := (congrArg (fun path => path.getLastD (pending semantics (emitted p))) check.started.split).trans
    (lastD_of_slice _ _ _ _)
  exact (congrArg (finished semantics (emitted p) input PUnit.unit) last).trans
    (recovered_result p input check.recovery)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Proofs

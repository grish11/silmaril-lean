module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Mathlib.Data.List.Chain

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending finished_no_step)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

local notation "rootStart" => pending semantics (emitted p)
local notation "entryValue" => entryBank (src := src) (entry := entry) input
local notation "enteredAt" => fun pre => atBody p pre entryValue (pending semantics (thetaBody p))

private theorem thereafter (start : RootMark p) (roots : List (RootMark p))
    (legal : List.IsChain (RootFire p input) (start :: roots))
    {bank : Bank (regs := regs) model}
    (done : finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics start) = some bank) :
    List.IsChain (ProfileStep p input) (start :: roots) := by
  induction roots generalizing start with
  | nil => exact .singleton _
  | cons after rest ih =>
    obtain ⟨fires, suffix⟩ := List.isChain_cons_cons.mp legal
    let cut := entryCut p
    have next : finished semantics (preheader p) input PUnit.unit (cut.observe semantics after) = some bank := by
      rcases cut.split_step semantics input PUnit.unit fires with ⟨step, _⟩ | ⟨same, _⟩
      · exact False.elim (finished_no_step semantics _ _ _ done step)
      · exact same ▸ done
    exact .cons_cons ⟨fires, fun _ _ => Option.isSome_iff_exists.mpr ⟨_, next⟩⟩ (ih after suffix next)

private theorem entry_profile (start : RootMark p) (roots : List (RootMark p))
    (entered : Entered p input start roots) (accepted : enter? p input start roots = some entered) :
    List.IsChain (ProfileStep p input) (start :: entered.earlier ++ [enteredAt entered.pre]) := by
  induction roots generalizing start with
  | nil => cases accepted
  | cons after rest ih =>
    simp only [enter?, bind, Option.bind] at accepted
    split at accepted
    · cases accepted
    · rename_i checked checkedEq
      split at accepted
      · cases accepted
      · rename_i stillPending
        dsimp only at accepted
        split at accepted
        · cases accepted
        · rename_i next found
          cases Option.some.inj accepted
          have stays : thetaPending p after = true := by unfold thetaPending; rw [stillPending]
          exact .cons_cons ⟨checked.down, fun _ ends => by rw [stays] at ends; cases ends⟩
            (ih after next found)
      · split at accepted
        · rename_i preDone
          split at accepted
          · rename_i fresh
            cases Option.some.inj accepted
            let pre := (entryCut p).observe semantics after
            have fires : RootFire p input start (enteredAt pre) :=
              Eq.mp (congrArg (RootFire p input start) fresh) checked.down
            have visible : (entryCut p).observe semantics (enteredAt pre) = pre :=
              (entryCut p).observe_attach semantics pre _
            exact .cons_cons ⟨fires, fun _ _ => Option.isSome_iff_exists.mpr
              ⟨_, (congrArg (finished semantics (preheader p) input PUnit.unit) visible).trans preDone⟩⟩
              (.singleton _)
          · cases accepted
        · cases accepted

theorem scan_sound (roots : List (RootMark p)) (accepted : (scan p input roots).isSome) :
    LegalComplete p input roots := by
  obtain ⟨checked, scanEq⟩ := Option.isSome_iff_exists.mp accepted
  have shape : enter? p input rootStart roots = some checked.started := by
    simp only [scan, bind, Option.bind] at scanEq
    split at scanEq
    · cases scanEq
    · rename_i started entryEq
      dsimp only at scanEq
      split at scanEq
      · cases scanEq
      · cases Option.some.inj scanEq
        exact entryEq
  let first := enteredAt checked.started.pre
  have entryTrace := entry_profile p input rootStart roots checked.started shape
  have endTrace : List.IsChain (RootFire p input) (first :: checked.started.remaining) := by
    apply List.IsChain.right_of_append (l₁ := rootStart :: checked.started.earlier)
    rw [List.cons_append, ← checked.started.split]
    exact checked.legal p input
  have afterEntry : finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics first) =
      some entryValue := by
    unfold first atBody
    rw [(entryCut p).observe_attach]
    exact checked.started.complete
  have suffix := thereafter p input first checked.started.remaining endTrace afterEntry
  have path := entryTrace.append_overlap (l₂ := [first]) suffix (List.cons_ne_nil _ _)
  refine ⟨?_, Option.isSome_iff_exists.mpr ⟨_, checked.returned p input⟩⟩
  rw [checked.started.split]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using path

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

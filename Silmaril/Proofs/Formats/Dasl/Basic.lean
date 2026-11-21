module

public import Silmaril.Formats.Dasl.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

variable {Name Next Last : Type}

theorem shallow_map_id (tree : Shallow Name) : Shallow.map id tree = tree := by
  induction tree with
  | ref link => cases link <;> rfl
  | obj name _ _ | blob name _ => exact name.elim
  | dict keys _ ih => exact congrArg (Tree.dict keys) (funext ih)
  | list len _ ih => exact congrArg (Tree.list len) (funext ih)
  | _ => rfl

theorem shallow_map_comp (first : Name → Next) (second : Next → Last) (tree : Shallow Name) :
    Shallow.map second (Shallow.map first tree) = Shallow.map (second ∘ first) tree := by
  induction tree with
  | ref link => cases link <;> rfl
  | obj name _ _ | blob name _ => exact name.elim
  | dict keys _ ih => exact congrArg (Tree.dict keys) (funext ih)
  | list len _ ih => exact congrArg (Tree.list len) (funext ih)
  | _ => rfl

theorem shallow_embed (tree : Shallow Name) : Partial.shallow tree.embed = tree := by
  induction tree with
  | obj name _ _ | blob name _ => exact name.elim
  | dict keys _ ih => exact congrArg (Tree.dict keys) (funext ih)
  | list len _ ih => exact congrArg (Tree.list len) (funext ih)
  | _ => rfl

theorem extends_trans {low mid high : Partial Name} (first : Extends low mid)
    (second : Extends mid high) : Extends low high := by
  induction first generalizing high with
  | same => exact second
  | openObj name target => cases second <;> exact .openObj name _
  | openBlob name target => cases second; exact .openBlob name target
  | obj name step ih =>
    cases second with
    | same => exact .obj name step
    | obj _ next => exact .obj name (ih next)
  | dict step ih =>
    cases second with
    | same => exact .dict step
    | dict next => exact .dict (fun key => ih key (next key))
  | list step ih =>
    cases second with
    | same => exact .list step
    | list next => exact .list (fun index => ih index (next index))

theorem extends_antisymm {low high : Partial Name} (first : Extends low high)
    (second : Extends high low) : low = high := by
  induction first with
  | same => rfl
  | openObj | openBlob => cases second
  | obj name _ ih =>
    cases second with
    | same => rfl
    | obj _ next => exact congrArg (Tree.obj name) (ih next)
  | dict _ ih =>
    cases second with
    | same => rfl
    | dict next => exact congrArg (Tree.dict _) (funext fun key => ih key (next key))
  | list _ ih =>
    cases second with
    | same => rfl
    | list next => exact congrArg (Tree.list _) (funext fun index => ih index (next index))

theorem extends_shallow_eq {low high : Partial Name} (step : Extends low high) :
    low.shallow = high.shallow := by
  induction step with
  | dict _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem shallow_le (tree : Partial Name) : Extends tree.shallow.embed tree := by
  induction tree with
  | obj name target _ => exact .openObj name target
  | blob name payload => exact .openBlob name payload
  | dict _ _ ih => exact .dict ih
  | list _ _ ih => exact .list ih
  | _ => exact .same _

theorem bindings_subset {low high : Partial Name} (step : Extends low high) :
    low.bindings.Subset high.bindings := by
  induction step with
  | same => exact ⟨by intro name payload hit; exact hit, by intro name payload hit; exact hit⟩
  | openObj | openBlob =>
    exact ⟨by intro name payload hit; exact hit.elim, by intro name payload hit; exact hit.elim⟩
  | obj name child ih =>
    refine ⟨?_, ih.2⟩
    intro key value hit
    rcases hit with ⟨same, view⟩ | deeper
    · exact Or.inl ⟨same, view.trans (extends_shallow_eq child)⟩
    · exact Or.inr (ih.1 deeper)
  | dict _ ih | list _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro name value ⟨index, hit⟩
    · exact ⟨index, (ih index).1 hit⟩
    · exact ⟨index, (ih index).2 hit⟩

end Silmaril.Proofs.Formats.Dasl

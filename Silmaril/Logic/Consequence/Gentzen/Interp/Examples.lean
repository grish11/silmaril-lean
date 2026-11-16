module

public import Silmaril.Logic.Consequence.Gentzen.Interp.Thms

/-!
# Examples: closure of interpretations and undefined readings

The interpretation that is undefined everywhere stays undefined when closed, so its `orBot`
reading is `⊥`; but the closure of `⊥` under reflexivity derives `[true] ⊢ [true]`
(`orBot_closure_ne`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.GInterp.Examples

/-- Closing an undefined reading is not closing `⊥`. -/
theorem orBot_closure_ne :
    Interp.orBot (closure (fun _ => defaultRules) (fun _ _ => none :
        GInterp PUnit.{1} PUnit.{1} fun _ => Bool)) () () ≠
      Derives defaultRules (Interp.orBot (fun _ _ => none :
        GInterp PUnit.{1} PUnit.{1} fun _ => Bool) () ()) := fun h => by
  have : Derives defaultRules (Interp.orBot (fun _ _ => none :
      GInterp PUnit.{1} PUnit.{1} fun _ => Bool) () ()) [true] [true] :=
    .refl trivial (List.mem_singleton_self _) (List.mem_singleton_self _)
  rw [← h] at this
  simp [Interp.orBot, closure, Interp.map, sysOrBot] at this

end Silmaril.Consequence.Gentzen.GInterp.Examples

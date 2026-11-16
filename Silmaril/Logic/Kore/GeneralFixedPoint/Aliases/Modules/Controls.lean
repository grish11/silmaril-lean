module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Modules.Examples

@[expose] public section
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleControls

def single (declarations : String) : String :=
  "[] module M sort S{} [] " ++ declarations ++ " endmodule []"

/-- An unused recursive alias still fails complete module validation. -/
theorem unused_cycle_rejected :
    (Modules.checkText 16 (single
      "alias loop{}(S{}):S{} where loop{}(E:S{}) := loop{}(E:S{}) []")).isSome = false := by
  decide +kernel

theorem alias_extra_free_object_rejected :
    (Modules.checkText 16 (single
      "alias extra{}(S{}):S{} where extra{}(E:S{}) := F:S{} []")).isSome = false := by
  decide +kernel

theorem alias_extra_free_set_rejected :
    (Modules.checkText 16 (single
      "alias extra{}(S{}):S{} where extra{}(E:S{}) := @F:S{} []")).isSome = false := by
  decide +kernel

theorem alias_negative_recursion_rejected :
    (Modules.checkText 16 (single
      "alias bad{}(S{}):S{} where bad{}(E:S{}) := \\mu{}(@X:S{},\\not{S{}}(@X:S{})) []")).isSome = false := by
  decide +kernel

theorem alias_duplicate_formals_rejected :
    (Modules.checkText 16 (single
      "alias dup{}(S{},S{}):S{} where dup{}(E:S{},E:S{}) := E:S{} []")).isSome = false := by
  decide +kernel

theorem alias_profile_mismatch_rejected :
    (Modules.checkText 16 (single
      "alias wrong{}():S{} where wrong{}(E:S{}) := E:S{} []")).isSome = false := by
  decide +kernel

theorem alias_wrong_actual_arity_rejected :
    (Modules.checkText 16 (single
      "alias id{}(S{}):S{} where id{}(E:S{}) := E:S{} [] axiom{} id{}() []")).isSome = false := by
  decide +kernel

theorem hidden_alias_rejected :
    (Modules.checkText 24
      "[] module BASE sort S{} [] alias id{}(S{}):S{} where id{}(E:S{}) := E:S{} [] endmodule [] module USE axiom{} id{}(\\top{S{}}()) [] endmodule []").isSome = false := by
  decide +kernel

theorem trailing_tokens_rejected :
    (Modules.parse (ModuleExamples.source ++ " trailing")).isSome = false := by decide +kernel

end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.ModuleControls

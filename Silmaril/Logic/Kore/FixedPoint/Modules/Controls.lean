module

public import Silmaril.Logic.Kore.FixedPoint.Modules.Examples

@[expose] public section
namespace Silmaril.Logic.Kore.FixedPoint.ModuleControls
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A symbol in the global ambient signature is unavailable without an import. -/
theorem hidden_symbol_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 symbol seed{}():S{} []
endmodule []
module USE
 sort T{} []
 axiom{} seed{}() []
endmodule []").isNone = true := by decide +kernel

theorem late_import_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
endmodule []
module USE
 claim{} \\top{S{}}() []
 import BASE []
endmodule []").isNone = true := by decide +kernel

theorem forward_import_rejected : (Modules.checkText 32 "[]
module USE
 import BASE []
endmodule []
module BASE
 sort S{} []
endmodule []").isNone = true := by decide +kernel

theorem duplicate_global_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
endmodule []
module USE
 sort S{} []
endmodule []").isNone = true := by decide +kernel

theorem aliases_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 alias hold{}(S{}):S{} where hold{}(X:S{}):=X:S{} []
endmodule []").isNone = true := by decide +kernel

theorem negative_occurrence_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 axiom{} \\mu{}(@X:S{},\\not{S{}}(@X:S{})) []
endmodule []").isNone = true := by decide +kernel

theorem conflicting_free_sorts_rejected : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 sort T{} []
 axiom{} \\and{S{}}(X:S{},\\exists{S{}}(Y:T{},X:T{})) []
endmodule []").isNone = true := by decide +kernel

theorem free_names_accepted : (Modules.checkText 32 "[]
module BASE
 sort S{} []
 axiom{} \\and{S{}}(X:S{},@X:S{}) []
endmodule []").isSome = true := by decide +kernel

/-- Set-name tokens cannot become ordinary declaration or module names. -/
theorem set_named_sort_rejected : (Modules.checkText 32 "[]
module BASE
 sort @S{} []
endmodule []").isNone = true := by decide +kernel

theorem set_named_module_rejected : (Modules.checkText 32 "[]
module @BASE
 sort S{} []
endmodule []").isNone = true := by decide +kernel

def diamondSource : String := "[]
module BASE
 sort S{} []
 symbol seed{}():S{} []
 axiom{} \\nu{}(@X:S{},@X:S{}) []
endmodule []
module LEFT
 import BASE []
endmodule []
module RIGHT
 import BASE []
endmodule []
module JOIN
 import LEFT []
 import RIGHT []
 claim{} \\mu{}(@X:S{},@X:S{}) []
endmodule []"

theorem diamond_checked : (Modules.checkText 32 diamondSource).isSome = true := by decide +kernel

def diamond : Modules.CheckedDefinition := (Modules.checkText 32 diamondSource).get diamond_checked
def base : Modules.CheckedModule diamond.ambient := diamond.modules.get ⟨0, by decide +kernel⟩
def left : Modules.CheckedModule diamond.ambient := diamond.modules.get ⟨1, by decide +kernel⟩
def right : Modules.CheckedModule diamond.ambient := diamond.modules.get ⟨2, by decide +kernel⟩
def join : Modules.CheckedModule diamond.ambient := diamond.modules.get ⟨3, by decide +kernel⟩

theorem diamond_one_symbol : join.scope.symbols.length = 1 := by decide +kernel

theorem diamond_origin : (join.axioms.map Kore.Modules.Checking.CheckedSentence.origin) =
    [⟨"BASE", 2⟩, ⟨"BASE", 2⟩] := by decide +kernel

theorem diamond_claim_separate : join.claims.length = 1 ∧ join.localAxioms.length = 0 :=
  by decide +kernel

theorem base_left : base.asImport ∈ left.imports := by
  change base.asImport ∈ [base.asImport]
  exact List.mem_singleton_self _

theorem base_right : base.asImport ∈ right.imports := by
  change base.asImport ∈ [base.asImport]
  exact List.mem_singleton_self _

theorem left_join : left.asImport ∈ join.imports := by
  change left.asImport ∈ [left.asImport, right.asImport]
  exact List.mem_cons_self

theorem right_join : right.asImport ∈ join.imports := by
  change right.asImport ∈ [left.asImport, right.asImport]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

open CategoryTheory Kore.Modules.Checking.CheckedModule in
theorem diamond_commutes :
    importHom base left base_left ≫ importHom left join left_join =
      importHom base right base_right ≫ importHom right join right_join :=
  import_diamond base left right join base_left base_right left_join right_join

open CategoryTheory in
theorem native_diamond_commutes :
    Modules.nativeImportHom base left base_left ≫ Modules.nativeImportHom left join left_join =
      Modules.nativeImportHom base right base_right ≫ Modules.nativeImportHom right join right_join := by
  apply Silmaril.Logic.Institution.Presentation.hom_ext
  rfl

end Silmaril.Logic.Kore.FixedPoint.ModuleControls

module

public import Silmaril.Logic.Egglog.Source.Named.Declarations.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named

instance (name : String) : Decidable (LegalName name) := by
  unfold LegalName Smt.SExpr.Writer.LegalAtom Smt.SExpr.Writer.LegalChar
  infer_instance

instance (D : DeclarationData) : Decidable D.Valid := by
  unfold DeclarationData.Valid
  infer_instance

/-- Check all declaration names, kind separation and profiles using only finite
local strings. No ambient signature or semantic carrier is inspected. -/
def DeclarationData.check (D : DeclarationData) : Option Declarations :=
  if h : D.Valid then some ⟨D, h⟩ else none

@[simp] theorem DeclarationData.check_eq_none (D : DeclarationData) :
    D.check = none ↔ ¬ D.Valid := by
  unfold check
  split <;> simp_all

/-- Header order within each symbol kind is retained; no declaration is dropped. -/
def DeclarationData.collect : List RawDeclaration → DeclarationData
  | [] => ⟨[], [], [], []⟩
  | .sort name :: rest =>
      let tail := collect rest
      { tail with sorts := name :: tail.sorts }
  | .constructor d :: rest =>
      let tail := collect rest
      { tail with constructors := d :: tail.constructors }
  | .relation d :: rest =>
      let tail := collect rest
      { tail with relations := d :: tail.relations }
  | .function d :: rest =>
      let tail := collect rest
      { tail with functions := d :: tail.functions }

def checkDeclarations (header : List RawDeclaration) : Option Declarations :=
  (DeclarationData.collect header).check

/-- The entire ordered binder context must have unique names, legal variable
names and declared sorts. The final list is never occurrence-pruned. -/
def Context.Valid (D : Declarations) (bindings : Context) : Prop :=
  (bindings.map Binding.name).Nodup ∧
  (∀ b ∈ bindings, LegalName b.name) ∧
  (∀ b ∈ bindings, b.sort ∈ D.data.sorts)

instance (D : Declarations) (bindings : Context) : Decidable (Context.Valid D bindings) := by
  unfold Context.Valid
  infer_instance

def Context.check (D : Declarations) (bindings : Context) : Option (CheckedContext D) :=
  if h : Context.Valid D bindings then
    some ⟨bindings, h.1, fun _i => h.2.2 _ (List.get_mem _ _)⟩
  else none

@[simp] theorem Context.check_eq_none (D : Declarations) (bindings : Context) :
    Context.check D bindings = none ↔ ¬ Context.Valid D bindings := by
  unfold check
  split <;> simp_all

end Silmaril.Logic.Egglog.Source.Named

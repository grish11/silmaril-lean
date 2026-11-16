module

public import Silmaril.Logic.Egg.Source.Named.Syntax.Defs
public import Silmaril.Logic.Egglog.Source.Named.Resolution.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named

/-- Collected occurrences retain exact constructor profiles. Duplicates are
removed only after collection; different profiles with the same name remain
and fail the existing declaration validity checker. -/
structure Support where
  sorts : List String
  constructors : List Silmaril.Logic.Egglog.Source.Named.TotalDeclaration

def Support.append (a b : Support) : Support :=
  ⟨a.sorts ++ b.sorts, a.constructors ++ b.constructors⟩

def Support.concat (xs : List Support) : Support :=
  xs.foldr Support.append ⟨[], []⟩

/-- Returns the inferred result sort together with every nested occurrence.
Variable sorts come from the explicit binders, not an ambient naming oracle. -/
def RawTerm.infer? (Γ : Silmaril.Logic.Egglog.Source.Named.Context) : RawTerm → Option (String × Support)
  | .var name => do
      let binding ← Γ.find? (fun b => b.name == name)
      pure (binding.sort, ⟨[binding.sort], []⟩)
  | .app name result n arguments => do
      let children ← Silmaril.Logic.Egglog.Source.Named.sequence? n (fun i => (arguments i).infer? Γ)
      let support := Support.concat (List.ofFn (fun i => (children i).2))
      pure (result, ⟨result :: support.sorts,
        ⟨name, List.ofFn (fun i => (children i).1), result⟩ :: support.constructors⟩)

def RawEquality.support? (Γ : Silmaril.Logic.Egglog.Source.Named.Context) (e : RawEquality) : Option Support := do
  let left ← e.left.infer? Γ
  let right ← e.right.infer? Γ
  if left.1 = right.1 then pure (left.2.append right.2) else none

def RawRule.support? (r : RawRule) : Option Support := do
  let guards ← r.guards.mapM (RawEquality.support? r.context)
  let conclusion ← r.conclusion.support? r.context
  pure ((⟨r.context.map Silmaril.Logic.Egglog.Source.Named.Binding.sort, []⟩ : Support).append
    ((Support.concat guards).append conclusion))

/-- Genuine inferred mode: no supplied declarations occur in this computation.
All binder sorts, even unused ones, enter the finite signature. -/
def inferDeclarations? (p : RawProgram) : Option Declarations := do
  let supports ← p.mapM RawRule.support?
  let support := Support.concat supports
  let data := Silmaril.Logic.Egglog.Source.Named.DeclarationData.mk support.sorts.eraseDups
    support.constructors.eraseDups [] []
  if h : data.Valid then pure ⟨⟨data, h⟩, rfl, rfl⟩ else none

end Silmaril.Logic.Egg.Source.Named

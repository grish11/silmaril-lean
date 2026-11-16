module

public import Silmaril.Logic.Egg.Source.Named.Inference.Defs
public import Silmaril.Logic.Egg.Source.Named.Denotation.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named

abbrev PackedTerm {D : Declarations} (Γ : CheckedContext D) :=
  Silmaril.Logic.Egglog.Source.Named.PackedTerm Γ

/-- Supplied mode verifies every authored result annotation against the actual
constructor declaration. Argument order and exact arity are checked recursively. -/
def resolveTerm? {D : Declarations} (Γ : CheckedContext D) :
    RawTerm → Option (PackedTerm Γ)
  | .var name => Silmaril.Logic.Egglog.Source.Named.resolveTerm? Γ (.var name)
  | .app name result n arguments => do
      let ⟨w, s, o⟩ ← Silmaril.Logic.Egglog.Source.Named.constructor? D.checked name n
      if s.val = result then
        let values ← Silmaril.Logic.Egglog.Source.Named.sequence? n (fun i => do
          let value ← resolveTerm? Γ (arguments i)
          Silmaril.Logic.Egglog.Source.Named.termAt? (w i) value)
        pure ⟨s, .app o values⟩
      else none

def resolveEquality? {D : Declarations} (Γ : CheckedContext D)
    (e : RawEquality) : Option (Core.Equality D.signature Γ.profile) := do
  let ⟨s, left⟩ ← resolveTerm? Γ e.left
  let right ← resolveTerm? Γ e.right
  let right ← Silmaril.Logic.Egglog.Source.Named.termAt? s right
  pure ⟨s, left, right⟩

def resolveRule? (D : Declarations) (r : RawRule) : Option (Core.Rule D.signature) := do
  let Γ ← Silmaril.Logic.Egglog.Source.Named.Context.check D.checked r.context
  let guards ← r.guards.mapM (resolveEquality? Γ)
  let conclusion ← resolveEquality? Γ r.conclusion
  pure ⟨Γ.bindings.length, Γ.profile, guards, conclusion⟩

/-- Whole-file checking also checks labels. No unchecked trailing rule is lost. -/
def resolveProgram? (D : Declarations) (p : RawProgram) :
    Option (List (Core.Rule D.signature)) :=
  if (p.map RawRule.name).Nodup ∧
      (∀ r ∈ p, Silmaril.Logic.Egglog.Source.Named.LegalName r.name) then
    p.mapM (resolveRule? D)
  else none

def inferProgram? (p : RawProgram) :
    Option (Σ D : Declarations, List (Core.Rule D.signature)) := do
  let D ← inferDeclarations? p
  let rules ← resolveProgram? D p
  pure ⟨D, rules⟩

end Silmaril.Logic.Egg.Source.Named

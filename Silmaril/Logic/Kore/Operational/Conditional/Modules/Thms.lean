module

public import Silmaril.Logic.Kore.Operational.Conditional.Modules.Defs
import Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.Modules

theorem visible_iff (p : CheckedDefinition) (target : String) (m : SourceModule) :
    m ∈ p.visible target ↔
      m ∈ p.source.modules ∧ ImportChain p.source.modules target m.name :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.visible_iff p target m

theorem declaration_iff (p : CheckedDefinition) (target : String) (d : Declaration) :
    d ∈ p.declarations target ↔
      ∃ m ∈ p.source.modules,
        ImportChain p.source.modules target m.name ∧ d ∈ m.declarations :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.declaration_iff p target d

theorem axiom_iff (p : CheckedDefinition) (target : String) (r : Rule) :
    r ∈ p.axioms target ↔
      ∃ m ∈ p.source.modules,
        ImportChain p.source.modules target m.name ∧
        ∃ d ∈ m.declarations,
          d.kind = .ruleAxiom ∧ ∃ Γ, elaborate d = some (Γ, r) :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.axiom_iff p target r

theorem all_declarations_checked (p : CheckedDefinition) {m : SourceModule}
    (hm : m ∈ p.source.modules) {d : Declaration} (hd : d ∈ m.declarations) :
    ∃ pair, elaborate d = some pair :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.all_declarations_checked p hm hd

theorem step_iff_source (p : CheckedDefinition) (target : String) (c d : Config) :
    Step (p.axioms target) c d ↔ SourceStep p.source target c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.step_iff_source p target c d

theorem successors_iff (p : CheckedDefinition) (target : String) (c d : Config) :
    d ∈ Execution.successors (p.axioms target) c ↔ SourceStep p.source target c d :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.successors_iff p target c d

theorem successors?_of_check {input target : String} {p : CheckedDefinition}
    (h : check input = some p) (ht : Present p.source.modules target) (c : Config) :
    successors? input target c = some (Execution.successors (p.axioms target) c) := by
  simp [successors?, h, ht]

/-- Success exposes the exact source-origin semantics for all Config, without
image restrictions, an externally supplied visibility premise, or claim rules. -/
theorem successors?_mem_iff {input target : String} {p : CheckedDefinition}
    (h : check input = some p) (ht : Present p.source.modules target) (c d : Config) :
    (∃ output, successors? input target c = some output ∧ d ∈ output) ↔
      SourceStep p.source target c d := by
  rw [successors?_of_check h ht]
  constructor
  · rintro ⟨output, ho, hd⟩
    have he : Execution.successors (p.axioms target) c = output := Option.some.inj ho
    subst output
    exact (successors_iff p target c d).1 hd
  · intro hd
    exact ⟨_, rfl, (successors_iff p target c d).2 hd⟩

/-- The generated prefix certificate passes for every structurally valid
earlier-import module graph. No certificate assumption is required from callers. -/
theorem resolve_complete (modules : List SourceModule)
    (ordered : OrderedFrom [] modules) : CertificateValid modules (resolve modules) :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules.resolve_complete modules ordered

/-- Every parsed ordered definition in the supported exact profile accepts. -/
theorem accepts_valid_profile
    {input : String} {source : Definition}
    (parsed : parse input = some source) (ordered : OrderedFrom [] source.modules)
    (profile : ProfileValid source) : ∃ p, check input = some p := by
  simp [check, parsed, ordered, profile, resolve_complete source.modules ordered]

/-- Rejected text and an unknown target both reject; a checked deadlock is some []. -/
theorem successors?_none_iff (input target : String) (c : Config) :
    successors? input target c = none ↔
      check input = none ∨ ∃ p, check input = some p ∧
        ¬ Present p.source.modules target := by
  cases h : check input with
  | none => simp [successors?, h]
  | some p =>
    by_cases ht : Present p.source.modules target <;> simp [successors?, h, ht]

end Silmaril.Logic.Kore.Operational.Conditional.Modules

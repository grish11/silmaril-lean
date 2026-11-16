module

public import Silmaril.Logic.ModalMu.Vector.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.ModalMu.Vector.Examples

/-- Genuine mutual recursion capturing a free outer set: X=P∪Y, Y=X. -/
def captured {S : Signature} : System S 1 := ⟨.disj (.var 2) (.var 1), .var 0⟩

theorem captured_mu {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    captured.denote false M ρ = (ρ 0, ρ 0) := by
  let op := captured.operator M ρ
  have upper : op.lfp ≤ (ρ 0, ρ 0) := by
    apply op.lfp_le
    change (ρ 0 ∪ ρ 0) ⊆ ρ 0 ∧ ρ 0 ⊆ ρ 0
    exact ⟨Set.union_subset le_rfl le_rfl, le_rfl⟩
  have first : ρ 0 ⊆ op.lfp.1 := by
    intro w hw
    have h : w ∈ (op op.lfp).1 := Or.inl hw
    exact (congrArg (fun P => w ∈ P.1) op.map_lfp).mp h
  have second : op.lfp.1 = op.lfp.2 := congrArg Prod.snd op.map_lfp
  have lower : (ρ 0, ρ 0) ≤ op.lfp := ⟨first, second ▸ first⟩
  exact le_antisymm upper lower

theorem captured_nu {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    captured.denote true M ρ = (Set.univ, Set.univ) := by
  apply le_antisymm le_top
  change (Set.univ, Set.univ) ≤ (captured.operator M ρ).gfp
  apply OrderHom.le_gfp
  change Set.univ ⊆ (ρ 0 ∪ Set.univ) ∧ Set.univ ⊆ Set.univ
  exact ⟨Set.subset_union_right, le_rfl⟩

/-- Both scalar outputs preserve the captured set for a simultaneous μ block. -/
theorem captured_scalar_mu {S : Signature} (M : Model S) (ρ : Env M.World 1) :
    ((captured.firstScalar false).denote M ρ, (captured.secondScalar false).denote M ρ) = (ρ 0, ρ 0) :=
  (captured.compile_correct false M ρ).trans (captured_mu M ρ)

/-- The same mutually recursive equations have a strictly different ν solution. -/
theorem empty_mu_full_nu {S : Signature} (M : Model S) :
    ((captured.firstScalar false).denote M (fun _ => ∅),
      (captured.secondScalar false).denote M (fun _ => ∅)) = (∅, ∅) ∧
    ((captured.firstScalar true).denote M (fun _ => ∅),
      (captured.secondScalar true).denote M (fun _ => ∅)) = (Set.univ, Set.univ) := by
  exact ⟨captured_scalar_mu M _, (captured.compile_correct true M _).trans (captured_nu M _)⟩

/-- Substitution images remain free beneath a μ and a ν, not just one binder. -/
theorem nested_substitution_capture {S : Signature} :
    ((.mu (.nu (.var 2)) : Formula S 1).substitute (fun _ => (.var 1 : Formula S 2))) =
      .mu (.nu (.var 3)) := rfl

def signature : Signature := ⟨Unit, Unit⟩

/-- X=p∨◇Y and Y=◇X are coupled, with distinct coordinate solutions on a toggle. -/
def alternating : System signature 0 :=
  ⟨.disj (.pos ()) (.diamond () (.var 1)), .diamond () (.var 0)⟩

def toggle : Model signature where
  World := Bool
  step _ w v := v = !w
  valuation _ := {false}
  point := false

theorem alternating_mu : alternating.denote false toggle emptyEnv = ({false}, {true}) := by
  let op := alternating.operator toggle emptyEnv
  have upper : op.lfp ≤ (({false} : Set Bool), ({true} : Set Bool)) := by
    apply op.lfp_le
    constructor
    · intro w hw
      rcases hw with h | ⟨v, hr, hv⟩
      · exact h
      · change w = false
        have hv' : v = true := hv
        cases w <;> simp_all [toggle]
    · intro w hw
      obtain ⟨v, hr, hv⟩ := hw
      change w = true
      have hv' : v = false := hv
      cases w <;> simp_all [toggle]
  have first : false ∈ op.lfp.1 := by
    have h : false ∈ (op op.lfp).1 := Or.inl rfl
    exact (congrArg (fun P => false ∈ P.1) op.map_lfp).mp h
  have second : true ∈ op.lfp.2 := by
    have h : true ∈ (op op.lfp).2 := ⟨false, rfl, first⟩
    exact (congrArg (fun P => true ∈ P.2) op.map_lfp).mp h
  have lower : (({false} : Set Bool), ({true} : Set Bool)) ≤ op.lfp := by
    constructor
    · intro w hw
      exact (show w = false from hw) ▸ first
    · intro w hw
      exact (show w = true from hw) ▸ second
  exact le_antisymm upper lower

theorem alternating_scalar :
    ((alternating.firstScalar false).denote toggle emptyEnv,
      (alternating.secondScalar false).denote toggle emptyEnv) = ({false}, {true}) :=
  (alternating.compile_correct false toggle emptyEnv).trans alternating_mu

def dead : Model signature where
  World := Unit
  step _ _ _ := False
  valuation _ := ∅
  point := ()

/-- Even a greatest simultaneous block cannot manufacture modal successors at
a deadlock. Both actual scalar outputs are empty in this model. -/
theorem dead_blocks (greatest : Bool) :
    ((alternating.firstScalar greatest).denote dead emptyEnv,
      (alternating.secondScalar greatest).denote dead emptyEnv) = (∅, ∅) := by
  let op := alternating.operator dead emptyEnv
  have constant (P : Set dead.World × Set dead.World) : op P = (∅, ∅) := by
    apply Prod.ext
    · apply Set.ext
      intro w
      change (False ∨ ∃ v : Unit, False ∧ v ∈ P.2) ↔ False
      simp
    · apply Set.ext
      intro w
      change (∃ v : Unit, False ∧ v ∈ P.1) ↔ False
      simp
  have unfold : op (fixed greatest op) = fixed greatest op := by
    cases greatest
    · exact op.map_lfp
    · exact op.map_gfp
  rw [constant] at unfold
  exact (alternating.compile_correct greatest dead emptyEnv).trans unfold.symm

end Silmaril.Logic.ModalMu.Vector.Examples

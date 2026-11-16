module

public import Silmaril.Logic.TypeTheory.LambdaPi.Signature.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi

/-- Inclusion is admissible in every hypothetical judgment. -/
theorem signature_derives_inclusion {S T : Signature} (h : S ⊆ T)
    {H : Set Judgment} {J : Judgment} (hd : Derives S.calculus H J) :
    Derives T.calculus H J := by
  have ht := (Signature.inclusion h).map_derives hd
  change Derives T.calculus (Judgment.mapConstants id '' H) (J.mapConstants id) at ht
  rw [judgment_map_id] at ht
  apply ht.bind
  rintro K ⟨L, hL, hLK⟩
  rw [judgment_map_id] at hLK
  exact hLK ▸ Derives.hyp hL

/-- A declaration's type remains sorted after later checked declarations are added. -/
theorem signature_declared_sorted {S : Signature} (h : S.Checked) {c : String} {A : Term}
    (hd : Declaration.mk c A ∈ S) : ∃ s, Derives S.calculus ∅ ⟨[], A, Term.univ s⟩ := by
  induction h with
  | nil => exact (List.not_mem_nil hd).elim
  | @cons S d B s previous fresh closed sorted ih =>
    have hsub : S ⊆ Declaration.mk d B :: S := fun _ hx => List.mem_cons_of_mem _ hx
    rcases List.mem_cons.mp hd with heq | htail
    · obtain ⟨rfl, rfl⟩ := Declaration.mk.inj heq
      exact ⟨s, signature_derives_inclusion hsub sorted⟩
    · obtain ⟨j, hj⟩ := ih htail
      exact ⟨j, signature_derives_inclusion hsub hj⟩

/-- Ordered signature checking rules out duplicate names. -/
theorem signature_nodup {S : Signature} (h : S.Checked) : (S.map Declaration.name).Nodup := by
  induction h with
  | nil => exact .nil
  | cons _ fresh _ _ ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi

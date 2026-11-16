module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.Paths
public import Silmaril.Proofs.Logic.Temporal.CTLStar.Renaming

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
open CategoryTheory Silmaril.Logic.Institution

theorem encodeCTL_holds {S : Signature} (M : Model S) (p : CTL.Formula S)
    (w : M.toModal.World) : (encodeCTL p).Holds M w ↔ p.Holds M w := by
  induction p generalizing w with
  | atom => rfl
  | bot => rfl
  | neg p ih => exact not_congr (ih w)
  | conj p q hp hq => exact and_congr (hp w) (hq w)
  | ex p ih =>
    change (∃ path : Path M.toModal.accessible,
      path.state 0 = w ∧ path.Valid 1 ∧ (encodeCTL p).Holds M (path.state 1)) ↔ _
    constructor
    · rintro ⟨path, h0, hv, hp⟩
      exact ⟨path.state 1, h0 ▸ path.edges 0 hv, (ih _).mp hp⟩
    · show (∃ v, M.toModal.accessible w v ∧ p.Holds M v) → _
      rintro ⟨v, hr, hp⟩
      show ∃ path : Path M.toModal.accessible, path.state 0 = w ∧
        path.Valid 1 ∧ (encodeCTL p).Holds M (path.state 1)
      let seq : Nat → M.toModal.World := fun i => if i = 0 then w else v
      have edges : ∀ i, i < 1 → M.toModal.accessible (seq i) (seq (i+1)) := by
        intro i hi
        have he : i = 0 := by omega
        simpa only [seq, he, ite_true, Nat.zero_add, Nat.one_ne_zero, ite_false] using hr
      obtain ⟨path, he, hv⟩ := Path.maximal_extension 1 seq edges
      refine ⟨path, he 0 (by omega), hv, ?_⟩
      rw [he 1 le_rfl]
      exact (ih v).mpr hp
  | eu p q hp hq =>
    change (∃ path : Path M.toModal.accessible, path.state 0 = w ∧
      ∃ n, path.Valid (0+n) ∧ (encodeCTL q).Holds M (path.state (0+n)) ∧
        ∀ i, i < n → (encodeCTL p).Holds M (path.state (0+i))) ↔ _
    simp only [Nat.zero_add]
    change _ ↔ CTL.Until _ _ _ w
    rw [CTL.until_iff_finite_prefix]
    constructor
    · rintro ⟨path, h0, n, hv, hq', hp'⟩
      refine ⟨n, path.state, h0, (hq _).mp hq', ?_⟩
      intro i hi
      exact ⟨(hp _).mp (hp' i hi), path.edges i (path.valid_of_le hv (by omega))⟩
    · rintro ⟨n, seq, h0, hq', hp'⟩
      obtain ⟨path, he, hv⟩ := Path.maximal_extension n seq (fun i hi => (hp' i hi).2)
      refine ⟨path, (he 0 (Nat.zero_le n)).trans h0, n, hv, ?_, ?_⟩
      · simpa only [Nat.zero_add, he n le_rfl] using (hq _).mpr hq'
      · intro i hi
        simpa only [Nat.zero_add, he i (Nat.le_of_lt hi)] using (hp _).mpr (hp' i hi).1
  | eg p ih =>
    change (∃ path : Path M.toModal.accessible, path.state 0 = w ∧
      (PathFormula.globally (.state (encodeCTL p))).Holds M path 0 ∧
        PathFormula.infinite.Holds M path 0) ↔ _
    constructor
    · rintro ⟨path, h0, hg, hinf⟩
      have hn := (PathFormula.infinite_iff M path).mp hinf
      have hall := (PathFormula.globally_iff M _ path 0).mp hg
      refine ⟨path.state, h0, fun n => path.edges n (by simp only [ValidIndex, hn]), ?_⟩
      intro n
      have h := hall n (by simp only [Path.Valid, ValidIndex, hn])
      exact (ih _).mp (by simpa only [Nat.zero_add, PathFormula.Holds] using h)
    · rintro ⟨seq, h0, hr, hp⟩
      let path : Path M.toModal.accessible :=
        ⟨seq, none, fun n _ => hr n, fun _ h => by cases h⟩
      refine ⟨path, h0, (PathFormula.globally_iff M _ path 0).mpr ?_,
        (PathFormula.infinite_iff M path).mpr rfl⟩
      intro n _
      simpa only [Nat.zero_add, PathFormula.Holds] using (ih _).mpr (hp n)

theorem encodeCTL_map {S T : Signature} (f : S ⟶ T) (p : CTL.Formula S) :
    encodeCTL (p.map f) = (encodeCTL p).map f := by
  induction p <;> simp_all only [CTL.Formula.map, encodeCTL, StateFormula.map,
    PathFormula.map, PathFormula.globally, PathFormula.eventually, PathFormula.top,
    StateFormula.top, PathFormula.infinite]

/-- The trace observed along an actual infinite path, without adding path quantifiers. -/
def trace {S : Signature} (M : Model S) (path : Path M.toModal.accessible) : LTL.Model S.Atom :=
  ULift.up (fun n a => M.toModal.valuation a (path.state n))

theorem encodeLTL_holds {S : Signature} (M : Model S) (path : Path M.toModal.accessible)
    (hinf : path.last = none) (p : LTL.Formula S.Atom) (i : Nat) :
    (encodeLTL p).Holds M path i ↔ p.Holds (trace M path) i := by
  classical
  induction p generalizing i with
  | atom => rfl
  | bot => rfl
  | not p ih => exact not_congr (ih i)
  | imp p q hp hq =>
    change (¬ ((encodeLTL p).Holds M path i ∧ ¬ (encodeLTL q).Holds M path i)) ↔ _
    rw [hp, hq]
    simp only [LTL.Formula.Holds]
    tauto
  | and p q hp hq => exact and_congr (hp i) (hq i)
  | or p q hp hq =>
    change (¬ (¬ (encodeLTL p).Holds M path i ∧ ¬ (encodeLTL q).Holds M path i)) ↔ _
    rw [hp, hq]
    simp only [LTL.Formula.Holds]
    tauto
  | next p ih =>
    change (path.Valid (i+1) ∧ _) ↔ _
    simp only [Path.Valid, ValidIndex, hinf, true_and]
    exact ih (i+1)
  | «until» p q hp hq =>
    change (∃ d, path.Valid (i+d) ∧ _ ∧ _) ↔ _
    simp only [Path.Valid, ValidIndex, hinf, true_and]
    exact exists_congr fun d => and_congr (hq (i+d))
      (forall_congr' fun j => imp_congr_right fun _ => hp (i+j))

theorem encodeLTL_map {S T : Signature} (f : S ⟶ T) (p : LTL.Formula S.Atom) :
    encodeLTL (p.map f) = (encodeLTL p).map f := by
  induction p <;> simp_all only [LTL.Formula.map, encodeLTL, StateFormula.map, PathFormula.map]

end Silmaril.Logic.Temporal.CTLStar

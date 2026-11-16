module

public import Silmaril.Logic.Temporal.CTLStar.Infinite.Defs
public import Silmaril.Logic.Temporal.CTLStar.Path.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar

mutual
/-- Full state syntax agrees with the source infinite-computation convention on serial frames. -/
theorem StateFormula.holds_infinite {S : Signature} (M : Model S)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) (p : StateFormula S)
    (w : M.toModal.World) : p.Holds M w ↔ p.InfiniteHolds M w := by
  cases p with
  | atom => rfl
  | bot => rfl
  | neg p => exact not_congr (p.holds_infinite M serial w)
  | conj p q => exact and_congr (p.holds_infinite M serial w) (q.holds_infinite M serial w)
  | existsPath p =>
    constructor
    · rintro ⟨path, h0, hp⟩
      have hn := path.last_none_of_serial serial
      exact ⟨path.state, h0, fun n => path.edges n (by simp only [ValidIndex, hn]),
        (p.holds_infinite M serial path hn 0).mp hp⟩
    · rintro ⟨seq, h0, he, hp⟩
      let path : Path M.toModal.accessible :=
        ⟨seq, none, fun n _ => he n, fun _ h => by cases h⟩
      exact ⟨path, h0, (p.holds_infinite M serial path rfl 0).mpr hp⟩

/-- Infinite path formulas use all states, with ordinary strong next and until. -/
theorem PathFormula.holds_infinite {S : Signature} (M : Model S)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) (p : PathFormula S)
    (path : Path M.toModal.accessible) (hinf : path.last = none) (i : Nat) :
    p.Holds M path i ↔ p.InfiniteHolds M path.state i := by
  cases p with
  | state p => exact p.holds_infinite M serial (path.state i)
  | neg p => exact not_congr (p.holds_infinite M serial path hinf i)
  | conj p q =>
    exact and_congr (p.holds_infinite M serial path hinf i)
      (q.holds_infinite M serial path hinf i)
  | next p =>
    change (path.Valid (i+1) ∧ _) ↔ _
    simp only [Path.Valid, ValidIndex, hinf, true_and]
    exact p.holds_infinite M serial path hinf (i+1)
  | «until» p q =>
    change (∃ d, path.Valid (i+d) ∧ _ ∧ _) ↔ _
    simp only [Path.Valid, ValidIndex, hinf, true_and]
    exact exists_congr fun d => and_congr (q.holds_infinite M serial path hinf (i+d))
      (forall_congr' fun j => imp_congr_right fun _ => p.holds_infinite M serial path hinf (i+j))
end

end Silmaril.Logic.Temporal.CTLStar

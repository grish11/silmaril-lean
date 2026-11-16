module

public import Silmaril.Logic.HybridPolyadic.Matching.Defs

public section
noncomputable section
namespace Silmaril.Proofs.Logic.HybridPolyadic.Matching
open CategoryTheory
open Silmaril.Logic.HybridPolyadic Silmaril.Logic.HybridPolyadic.Matching
open Silmaril.Logic.Matching

variable {S : Signature} (M : Silmaril.Logic.HybridPolyadic.Matching.Model S)

private theorem nullary_denote {n : ℕ} (op : Operation S 0 Fin.elim0 ())
    (env : Fin n → M.base.carrier ()) (w : M.base.carrier ()) :
    w ∈ M.base.denote env (.app op (fun i => i.elim0)) ↔
      w ∈ M.base.operation op (fun i => i.elim0) := by
  constructor
  · rintro ⟨values, _, hr⟩
    have he : values = (fun i => i.elim0) := funext (fun i => Fin.elim0 i)
    simpa only [he] using hr
  · intro hr
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hr⟩

/-- Nominal singleton semantics follows from the actual nullary operation equation. -/
theorem nominal_denote {n : ℕ} (a : S.Nominal) (env : Fin n → M.base.carrier ())
    (w : M.base.carrier ()) : w ∈ M.base.denote env (nominalPattern a) ↔ w = M.name a := by
  rw [nominalPattern, nullary_denote, M.nominal]
  rfl

/-- The fixed marked δ graph yields global existential definedness. -/
theorem defined_denote {n : ℕ} (p : Pattern S n) (env : Fin n → M.base.carrier ())
    (w : M.base.carrier ()) :
    w ∈ M.base.denote env (definedPattern p) ↔ ∃ v, v ∈ M.base.denote env p := by
  constructor
  · rintro ⟨values, hs, _⟩
    exact ⟨values 0, hs 0⟩
  · rintro ⟨v, hv⟩
    refine ⟨fun _ => v, ?_, ?_⟩
    · intro i
      rw [Fin.eq_zero i]
      exact hv
    · rw [M.definedness]
      trivial

/-- The translation uses only raw matching set semantics and the marked operation laws. -/
theorem translate_denote {n : ℕ} (p : Formula S n) (env : Fin n → M.base.carrier ())
    (w : M.base.carrier ()) :
    w ∈ M.base.denote env (translate p) ↔ p.Holds (decode M) env w := by
  classical
  induction p generalizing w with
  | atom a =>
    rw [translate, nullary_denote]
    rfl
  | bot =>
    rw [translate, FirstOrder.Model.denote_bottom]
    rfl
  | imp p q hp hq =>
    change ¬ (w ∈ M.base.denote env (translate p) ∧ ¬ w ∈ M.base.denote env (translate q)) ↔ _
    rw [hp env w, hq env w]
    constructor
    · intro h hp
      by_contra hq
      exact h ⟨hp, hq⟩
    · intro h ⟨hp, hq⟩
      exact hq (h hp)
  | nominal a => exact nominal_denote M a env w
  | state i => rfl
  | atNom a p hp =>
    show _ ↔ p.Holds (decode M) env (M.name a)
    rw [translate, defined_denote]
    change (∃ v, v ∈ M.base.denote env (nominalPattern a) ∧ v ∈ M.base.denote env (translate p)) ↔ _
    constructor
    · rintro ⟨v, hn, hv⟩
      have he : v = M.name a := (nominal_denote M a env v).mp hn
      change p.Holds (decode M) env (M.name a)
      exact he ▸ (hp env v).mp hv
    · intro h
      exact ⟨M.name a, (nominal_denote M a env _).mpr rfl, (hp env _).mpr h⟩
  | atState i p hp =>
    rw [translate, defined_denote]
    change (∃ v, v = env i ∧ v ∈ M.base.denote env (translate p)) ↔ _
    simp only [exists_eq_left]
    exact hp env (env i)
  | dia a ps ih =>
    show (∃ vs, (∀ i, vs i ∈ M.base.denote env (translate (ps i))) ∧
      w ∈ M.base.operation (.action a) vs) ↔ _
    refine exists_congr fun vs => ?_
    constructor
    · rintro ⟨hs, hr⟩
      exact ⟨hr, fun i => (ih i env (vs i)).mp (hs i)⟩
    · rintro ⟨hr, hs⟩
      exact ⟨fun i => (ih i env (vs i)).mpr (hs i), hr⟩
  | down p hp =>
    show (∃ v, w = v ∧ w ∈ M.base.denote (Fin.cases v env) (translate p)) ↔ _
    constructor
    · rintro ⟨v, rfl, hv⟩
      exact (hp (Fin.cons w env) w).mp hv
    · intro h
      exact ⟨w, rfl, (hp (Fin.cons w env) w).mpr h⟩

end Silmaril.Proofs.Logic.HybridPolyadic.Matching

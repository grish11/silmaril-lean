module

public import Silmaril.Logic.SAT.Institution.Defs

public section

namespace Silmaril.Proofs.Logic.SAT.Institution

open Silmaril.Logic.SAT.Institution

universe u v w x
variable {A : Type u} {B : Type v}

theorem rename_id : Problem.rename (id : A → A) = id := by
  funext F
  have h : Literal.rename (id : A → A) = id := by funext l; cases l; rfl
  simp [Problem.rename, h]

theorem rename_comp {D : Type w} (f : A → B) (g : B → D) :
    Problem.rename (g ∘ f) = Problem.rename g ∘ Problem.rename f := by
  funext F
  simp [Problem.rename, List.map_map, Function.comp_def, Literal.rename]

theorem evalWith_rename {V : Type w} (top bot : V) (neg : V → V) (conj disj : V → V → V)
    (f : A → B) (v : B → V) (F : Problem A) :
    (F.rename f).evalWith top bot neg conj disj v = F.evalWith top bot neg conj disj (reduct f v) := by
  simp only [Problem.rename, Problem.evalWith, Clause.evalWith, List.foldr_map]
  rfl

private theorem evalWith_bool (v : TotalValuation A) (F : Problem A) :
    F.evalWith true false Bool.not Bool.and Bool.or v = F.eval v := by
  have clause (C : Clause A) :
      Clause.evalWith false Bool.not Bool.or v C = C.any (fun l => v l.atom == l.positive) := by
    induction C with
    | nil => rfl
    | cons l C ih =>
      have literal : l.evalWith Bool.not v = (v l.atom == l.positive) := by
        cases l with
        | mk a positive => cases positive <;> cases h : v a <;> simp [Literal.evalWith, h]
      simpa only [Clause.evalWith, List.foldr_cons, List.any_cons, literal] using
        congrArg (Bool.or (v l.atom == l.positive)) ih
  induction F with
  | nil => rfl
  | cons C F ih =>
    simpa only [Problem.evalWith, Problem.eval, List.foldr_cons, List.all_cons, clause] using
      congrArg (Bool.and (C.any fun l => v l.atom == l.positive)) ih

theorem eval_rename (f : A → B) (v : TotalValuation B) (F : Problem A) :
    (F.rename f).eval v = F.eval (reduct f v) := by
  simp only [Problem.rename, Problem.eval, List.all_map, List.any_map,
    Function.comp_def, Literal.rename, reduct]

theorem eval_ofCNF (v : TotalValuation Nat) (F : Silmaril.Logic.SAT.CNF) :
    (Problem.ofCNF F).eval v = Silmaril.Logic.SAT.CNF.eval v F := by
  simp only [Problem.ofCNF, Problem.eval, Silmaril.Logic.SAT.CNF.eval, List.all_map,
    List.any_map, Function.comp_def]
  rfl

private theorem evalWith_rel {V : Type w} {W : Type x} (R : V → W → Prop)
    {top bot : V} {top' bot' : W} {neg : V → V} {neg' : W → W}
    {conj disj : V → V → V} {conj' disj' : W → W → W}
    (htop : R top top') (hbot : R bot bot')
    (hneg : ∀ {a a'}, R a a' → R (neg a) (neg' a'))
    (hconj : ∀ {a a' b b'}, R a a' → R b b' → R (conj a b) (conj' a' b'))
    (hdisj : ∀ {a a' b b'}, R a a' → R b b' → R (disj a b) (disj' a' b'))
    {v : A → V} {v' : A → W} (hv : ∀ a, R (v a) (v' a)) (F : Problem A) :
    R (F.evalWith top bot neg conj disj v) (F.evalWith top' bot' neg' conj' disj' v') := by
  apply List.foldr_rel htop
  intro C _ acc acc' hacc
  refine hconj ?_ hacc
  apply List.foldr_rel hbot
  intro l _ rest rest' hrest
  refine hdisj ?_ hrest
  unfold Literal.evalWith
  split
  · exact hv l.atom
  · exact hneg (hv l.atom)

theorem evalK3_total (v : TotalValuation A) (F : Problem A) :
    F.evalK3 (some ∘ v) = some (F.eval v) := by
  rw [← evalWith_bool v F]
  symm
  refine evalWith_rel (fun b k => some b = k) rfl rfl ?_ ?_ ?_ (fun _ => rfl) F
  · rintro b _ rfl
    cases b <;> rfl
  · rintro b _ c _ rfl rfl
    cases b <;> cases c <;> rfl
  · rintro b _ c _ rfl rfl
    cases b <;> cases c <;> rfl

theorem evalEvidence_ofK3 (v : PartialValuation A) (F : Problem A) :
    F.evalEvidence (Evidence.ofK3 ∘ v) = Evidence.ofK3 (F.evalK3 v) := by
  symm
  refine evalWith_rel (fun k e => Evidence.ofK3 k = e) rfl rfl ?_ ?_ ?_ (fun _ => rfl) F
  · rintro (_ | (_ | _)) _ rfl <;> rfl
  · rintro (a | (a | a)) _ (b | (b | b)) _ rfl rfl <;> rfl
  · rintro (a | (a | a)) _ (b | (b | b)) _ rfl rfl <;> rfl

theorem evalK3_informationLE {v v' : PartialValuation A}
    (hv : ∀ a, K3.InformationLE (v a) (v' a)) (F : Problem A) :
    K3.InformationLE (F.evalK3 v) (F.evalK3 v') := by
  refine evalWith_rel K3.InformationLE (fun _ h => h) (fun _ h => h) ?_ ?_ ?_ hv F
  · intro a a' h
    rcases a with _ | a
    · simp [K3.InformationLE, K3.neg]
    · rw [h a rfl]
      exact fun _ he => he
  · intro a a' b b' ha hb
    rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;>
      simp_all [K3.InformationLE, K3.conj]
    rcases a' with _ | (_ | _) <;> rfl
  · intro a a' b b' ha hb
    rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;>
      simp_all [K3.InformationLE, K3.disj]
    rcases a' with _ | (_ | _) <;> rfl

theorem evalEvidence_informationLE {v v' : EvidenceValuation A}
    (hv : ∀ a, Evidence.InformationLE (v a) (v' a)) (F : Problem A) :
    Evidence.InformationLE (F.evalEvidence v) (F.evalEvidence v') := by
  have refl (e : Evidence) : e.InformationLE e := ⟨fun h => h, fun h => h⟩
  refine evalWith_rel Evidence.InformationLE (refl _) (refl _) ?_ ?_ ?_ hv F
  · exact fun h => ⟨h.2, h.1⟩
  · intro a a' b b' ha hb
    simp only [Evidence.InformationLE, Evidence.conj, Bool.and_eq_true, Bool.or_eq_true] at *
    exact ⟨fun h => ⟨ha.1 h.1, hb.1 h.2⟩, fun h => h.imp ha.2 hb.2⟩
  · intro a a' b b' ha hb
    simp only [Evidence.InformationLE, Evidence.disj, Bool.and_eq_true, Bool.or_eq_true] at *
    exact ⟨fun h => h.imp ha.1 hb.1, fun h => ⟨ha.2 h.1, hb.2 h.2⟩⟩

end Silmaril.Proofs.Logic.SAT.Institution

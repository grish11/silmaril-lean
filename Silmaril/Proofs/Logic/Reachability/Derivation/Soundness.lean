module

public import Silmaril.Proofs.Logic.Reachability.Derivation.Paths

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation

variable {J W ι : Type} {D : J → Type} {rules : ι → RuleSystem.Scheme W}

/-- Source Lemma 1, with vertex-count bounds. Both environments are positive;
C has one less vertex of fuel, and nonempty C forces a positive conclusion. -/
theorem Derives.bounded_sound {A C : Set (Claim D W)} {c : Claim D W}
    (d : Derives rules A C c) (wellDefined : RuleSystem.WeaklyWellDefined rules) :
    ∀ n, Environment (RuleSystem.Induced rules) true n A →
      Environment (RuleSystem.Induced rules) true (n - 1) C →
      Bounded (RuleSystem.Induced rules) false n c ∧
        (C.Nonempty → Bounded (RuleSystem.Induced rules) true n c) := by
  induction d with
  | @step A C P Q cover successors =>
      intro n hA hC
      have positive : Bounded (RuleSystem.Induced rules) true n ⟨P, Q⟩ := by
        intro a p hp hw
        obtain ⟨v, hv⟩ := RuleSystem.progress wellDefined (cover a) (p.point 0) hw
        have nonzero : p.length ≠ 0 := by
          intro hz
          have terminal := p.terminal v
          rw [hz] at terminal
          exact terminal hv
        have edge := p.edge 0 (by omega)
        exact ⟨1, by omega, RuleSystem.successors (successors a) hw edge, by simp⟩
      exact ⟨positive.weaken, fun _ => positive⟩
  | @useAxiom A C c member =>
      intro n hA hC
      exact ⟨(hA c member).weaken, fun _ => hA c member⟩
  | @reflexivity A P =>
      intro n hA hC
      constructor
      · intro a p hp hw
        exact ⟨0, Nat.zero_le _, hw, by simp⟩
      · rintro ⟨c, hc⟩
        exact False.elim hc
  | @transitivity A C P B Q first second ihFirst ihSecond =>
      intro n hA hC
      by_cases empty : C = ∅
      · have firstWeak := (ihFirst n hA hC).1
        have secondEnv : Environment (RuleSystem.Induced rules) true n (A ∪ C) := by
          simpa only [empty, Set.union_empty] using hA
        have secondWeak := (ihSecond n secondEnv (Environment.empty true (n - 1))).1
        constructor
        · intro a p hp hw
          obtain ⟨i, hi, hb, _⟩ := firstWeak a p hp hw
          apply Hit.shift p hi
          apply secondWeak a (p.suffix i hi)
          · change p.length - i + 1 ≤ n
            omega
          · simpa only [CompletePath.suffix, Nat.add_zero] using hb
        · intro nonempty
          rw [empty] at nonempty
          exact False.elim (Set.not_nonempty_empty nonempty)
      · have nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr empty
        have firstPositive := (ihFirst n hA hC).2 nonempty
        have secondEnv := Environment.union (hA.mono (by omega : n - 1 ≤ n)) hC
        have secondWeak := (ihSecond (n - 1) secondEnv
          (Environment.empty true (n - 1 - 1))).1
        have positive : Bounded (RuleSystem.Induced rules) true n ⟨P, Q⟩ := by
          intro a p hp hw
          obtain ⟨i, hi, hb, hpos⟩ := firstPositive a p hp hw
          have strict := hpos rfl
          apply Hit.shift_positive p hi strict
          apply secondWeak a (p.suffix i hi)
          · change p.length - i + 1 ≤ n - 1
            omega
          · simpa only [CompletePath.suffix, Nat.add_zero] using hb
        exact ⟨positive.weaken, fun _ => positive⟩
  | @cases A C P₁ P₂ Q left right ihLeft ihRight =>
      intro n hA hC
      have hl := ihLeft n hA hC
      have hr := ihRight n hA hC
      constructor
      · intro a p hp hw
        exact hw.elim (hl.1 a p hp) (hr.1 a p hp)
      · intro nonempty a p hp hw
        exact hw.elim (hl.2 nonempty a p hp) (hr.2 nonempty a p hp)
  | @abstraction A C P Q X inner independent ih =>
      intro n hA hC
      have result := ih n hA hC
      have transfer : ∀ δ, Bounded (RuleSystem.Induced rules) δ n ⟨P, Q⟩ →
          Bounded (RuleSystem.Induced rules) δ n ⟨Abstract X P, Q⟩ := by
        intro δ valid a p hp hw
        obtain ⟨b, agree, hb⟩ := hw
        obtain ⟨i, hi, hq, positive⟩ := valid b p hp hb
        exact ⟨i, hi, (independent a b agree (p.point i)).mpr hq, positive⟩
      exact ⟨transfer false result.1, fun nonempty => transfer true (result.2 nonempty)⟩
  | @consequence A C P Q P₀ Q₀ pre inner post ih =>
      intro n hA hC
      have result := ih n hA hC
      have transfer : ∀ δ, Bounded (RuleSystem.Induced rules) δ n ⟨P₀, Q₀⟩ →
          Bounded (RuleSystem.Induced rules) δ n ⟨P, Q⟩ := by
        intro δ valid a p hp hw
        obtain ⟨i, hi, hq, positive⟩ := valid a p hp (pre a (p.point 0) hw)
        exact ⟨i, hi, post a (p.point i) hq, positive⟩
      exact ⟨transfer false result.1, fun nonempty => transfer true (result.2 nonempty)⟩
  | @circularity A C c inner ihDerivation =>
      -- Strengthen the inner induction to positive validity even for C=∅.
      have positive : ∀ n, Environment (RuleSystem.Induced rules) true n A →
          Environment (RuleSystem.Induced rules) true (n - 1) C →
          Bounded (RuleSystem.Induced rules) true n c := by
        intro n
        induction n using Nat.strong_induction_on with
        | ind n ihFuel =>
            intro hA hC
            by_cases zero : n = 0
            · subst n
              exact Bounded.zero true c
            · have smaller : n - 1 < n := by omega
              have claimSmall := ihFuel (n - 1) smaller
                (hA.mono (by omega)) (hC.mono (by omega))
              have enlarged : Environment (RuleSystem.Induced rules) true (n - 1)
                  (C ∪ {c}) := by
                intro other member
                rcases member with old | added
                · exact hC other old
                · have same : other = c := Set.mem_singleton_iff.mp added
                  subst other
                  exact claimSmall
              exact (ihDerivation n hA enlarged).2 ⟨c, Or.inr rfl⟩
      intro n hA hC
      exact ⟨(positive n hA hC).weaken, fun _ => positive n hA hC⟩

/-- Source Theorem 1: no external axiom or circularity validity is assumed. -/
theorem Derives.sound {c : Claim D W} (d : Derives rules ∅ ∅ c)
    (wellDefined : RuleSystem.WeaklyWellDefined rules) :
    ∀ a w, c.pre a w → AllPartial (RuleSystem.Induced rules) (c.post a) w := by
  apply (bounded_all_iff c).mp
  intro n
  exact (d.bounded_sound wellDefined n (Environment.empty true n)
    (Environment.empty true (n - 1))).1

end Silmaril.Logic.Reachability.Derivation

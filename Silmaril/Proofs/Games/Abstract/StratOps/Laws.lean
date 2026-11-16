module

public import Silmaril.Games.Abstract.StratOps.Defs
public import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Operations on observation triples: laws (proofs)

The `(AFun, PInf)` parts are the `FullFun` laws; these proofs handle the pending component.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

theorem ext_full {t t' : ObsTriple E S A B} (hf : full t = full t') (hp : t.2.1 = t'.2.1) :
    t = t' :=
  Prod.ext (congrArg (fun F : FullFun E S A B => F.1) hf)
    (Prod.ext hp (congrArg (fun F : FullFun E S A B => F.2) hf))

theorem mem_seq_ret {f : AFun E S A B} {g : AFun E S B C} {s : S} {a : A}
    {d : List (Call E)} {c : C} {s' : S} :
    (d, End.ret c s') ∈ AFun.seq f g s a ↔
      ∃ c₁ b s₁ c₂, (c₁, End.ret b s₁) ∈ f s a ∧ (c₂, End.ret c s') ∈ g s₁ b ∧ d = c₁ ++ c₂ := by
  constructor
  · rintro (⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨c₁, b, s₁, c₂, e, hf, hg, he⟩)
    · cases (Prod.mk.inj he).2
    · cases (Prod.mk.inj he).2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨c₁, b, s₁, c₂, hf, hg, rfl⟩
  · rintro ⟨c₁, b, s₁, c₂, hf, hg, rfl⟩
    exact .inr (.inr ⟨c₁, b, s₁, c₂, _, hf, hg, rfl⟩)

theorem mem_map_ret {F : FullFun E S A B} {h : B → C} {s : S} {a : A} {c : List (Call E)}
    {b' : C} {s' : S} :
    (c, End.ret b' s') ∈ (F.map h).1 s a ↔ ∃ b, (c, End.ret b s') ∈ F.1 s a ∧ h b = b' := by
  rw [FullFun.mem_map]
  constructor
  · rintro ⟨c', e, hy, he⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    cases e with
    | ret b s₁ =>
      simp only [FullFun.endMap] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨b, hy, rfl⟩
    | trap => cases he
    | div => cases he
  · rintro ⟨b, hy, rfl⟩
    exact ⟨c, .ret b s', hy, rfl⟩

/-! ## Sequencing -/

theorem seqT_assoc (t : ObsTriple E S A B) (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqT (seqT t u) v = seqT t (seqT u v) := by
  refine ext_full (FullFun.seq_assoc _ _ _) (funext fun s => funext fun a => ?_)
  ext ⟨d, m⟩
  simp only [seqT, ofFull, full, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((h | ⟨c₁, b, s₁, c₂, m', hf, hg, he⟩) | ⟨c₁, c, s₂, c₃, m', hfg, hh, he⟩)
    · exact .inl h
    · exact .inr ⟨c₁, b, s₁, c₂, m', hf, .inl hg, he⟩
    · obtain ⟨d₁, b, s₁, d₂, hf, hg, rfl⟩ := mem_seq_ret.1 hfg
      exact .inr ⟨d₁, b, s₁, d₂ ++ c₃, m', hf, .inr ⟨d₂, c, s₂, c₃, m', hg, hh, rfl⟩,
        by rw [he, List.append_assoc]⟩
  · rintro (h | ⟨c₁, b, s₁, c₂, m', hf, hg | ⟨d₂, c, s₂, c₃, m'', hg, hh, he'⟩, he⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨c₁, b, s₁, c₂, m', hf, hg, he⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact .inr ⟨c₁ ++ d₂, c, s₂, c₃, m', mem_seq_ret.2 ⟨c₁, b, s₁, d₂, hf, hg, rfl⟩, hh,
        by rw [he, List.append_assoc]⟩

theorem seqT_pureT (t : ObsTriple E S A B) : seqT t pureT = t := by
  refine ext_full (FullFun.seq_pure _) (funext fun s => funext fun a => ?_)
  ext x
  simp only [seqT, pureT, ofFull, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    false_and, and_false, exists_false, or_false]

theorem pureT_seqT (u : ObsTriple E S A B) : seqT pureT u = u := by
  refine ext_full (FullFun.pure_seq _) (funext fun s => funext fun a => ?_)
  ext ⟨d, m⟩
  simp only [seqT, pureT, ofFull, FullFun.pure, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, Set.mem_singleton_iff, false_or]
  constructor
  · rintro ⟨c₁, b, s₁, c₂, m', he₁, hg, he⟩
    obtain ⟨rfl, hr⟩ := Prod.mk.inj he₁
    obtain ⟨rfl, rfl⟩ := End.ret.inj hr
    rw [he]
    exact hg
  · intro h
    exact ⟨[], a, s, d, m, rfl, h, rfl⟩

/-! ## Pure maps -/

theorem mapT_id (t : ObsTriple E S A B) : mapT t id = t :=
  ext_full (FullFun.map_id _) rfl

theorem mapT_mapT (t : ObsTriple E S A B) (h : B → C) (h' : C → D) :
    mapT (mapT t h) h' = mapT t (h' ∘ h) :=
  ext_full (FullFun.map_map _ _ _) rfl

theorem seqT_pureT_mapT (t : ObsTriple E S A B) (h : B → C) :
    seqT t (mapT pureT h) = mapT t h := by
  refine ext_full (FullFun.seq_pure_map _ _) (funext fun s => funext fun a => ?_)
  ext x
  simp [seqT, mapT, pureT, ofFull]

theorem pureT_mapT_seqT (h : A → B) (u : ObsTriple E S B C) :
    seqT (mapT pureT h) u = comapT u h := by
  refine ext_full (FullFun.pure_map_seq _ _) (funext fun s => funext fun a => ?_)
  ext ⟨d, m⟩
  simp only [seqT, mapT, pureT, comapT, ofFull, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, false_or]
  constructor
  · rintro ⟨c₁, b, s₁, c₂, m', he₁, hg, he⟩
    obtain ⟨b₀, hb, rfl⟩ := mem_map_ret.1 he₁
    obtain ⟨rfl, hr⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hb)
    obtain ⟨rfl, rfl⟩ := End.ret.inj hr
    rw [he]
    exact hg
  · intro hg
    exact ⟨[], h a, s, d, m, mem_map_ret.2 ⟨a, rfl, rfl⟩, hg, rfl⟩

theorem seqT_mapT (t : ObsTriple E S A B) (h : B → C) (u : ObsTriple E S C D) :
    seqT (mapT t h) u = seqT t (comapT u h) := by
  refine ext_full (FullFun.seq_map _ _ _) (funext fun s => funext fun a => ?_)
  ext ⟨d, m⟩
  simp only [seqT, mapT, comapT, ofFull, full, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (h₀ | ⟨c₁, c, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · obtain ⟨b, hb, rfl⟩ := mem_map_ret.1 hf
      exact .inr ⟨c₁, b, s₁, c₂, m', hb, hg, he⟩
  · rintro (h₀ | ⟨c₁, b, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · exact .inr ⟨c₁, h b, s₁, c₂, m', mem_map_ret.2 ⟨b, hf, rfl⟩, hg, he⟩

theorem mapT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) (h : C → D) :
    mapT (seqT t u) h = seqT t (mapT u h) :=
  ext_full (FullFun.map_seq _ _ _) rfl

/-! ## Whiskering -/

theorem whiskerRightT_pureT : whiskerRightT (pureT : ObsTriple E S A A) C = pureT :=
  ext_full FullFun.whiskerRight_pure rfl

theorem whiskerLeftT_pureT : whiskerLeftT C (pureT : ObsTriple E S A A) = pureT :=
  ext_full FullFun.whiskerLeft_pure rfl

theorem whiskerRightT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B D) (C : Type u) :
    whiskerRightT (seqT t u) C = seqT (whiskerRightT t C) (whiskerRightT u C) := by
  refine ext_full (FullFun.whiskerRight_seq _ _ _) (funext fun s => funext fun p => ?_)
  ext ⟨d, m⟩
  simp only [seqT, whiskerRightT, ofFull, full, FullFun.whiskerRight, Set.mem_union,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h₀ | ⟨c₁, b, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · exact .inr ⟨c₁, (b, p.2), s₁, c₂, m', mem_map_ret.2 ⟨b, hf, rfl⟩, hg, he⟩
  · rintro (h₀ | ⟨c₁, bc, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · obtain ⟨b, hb, rfl⟩ := mem_map_ret.1 hf
      exact .inr ⟨c₁, b, s₁, c₂, m', hb, hg, he⟩

theorem whiskerLeftT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B D) (C : Type u) :
    whiskerLeftT C (seqT t u) = seqT (whiskerLeftT C t) (whiskerLeftT C u) := by
  refine ext_full (FullFun.whiskerLeft_seq _ _ _) (funext fun s => funext fun p => ?_)
  ext ⟨d, m⟩
  simp only [seqT, whiskerLeftT, ofFull, full, FullFun.whiskerLeft, Set.mem_union,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h₀ | ⟨c₁, b, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · exact .inr ⟨c₁, (p.1, b), s₁, c₂, m', mem_map_ret.2 ⟨b, hf, rfl⟩, hg, he⟩
  · rintro (h₀ | ⟨c₁, bc, s₁, c₂, m', hf, hg, he⟩)
    · exact .inl h₀
    · obtain ⟨b, hb, rfl⟩ := mem_map_ret.1 hf
      exact .inr ⟨c₁, b, s₁, c₂, m', hb, hg, he⟩

/-- The interchange law fails for triples: the full observations already differ. -/
theorem not_interchangeT :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      seqT (whiskerRightT t PUnit) (whiskerLeftT PUnit u) ≠
        seqT (whiskerLeftT PUnit u) (whiskerRightT t PUnit) := by
  obtain ⟨E, f, g, h⟩ := FullFun.not_interchange
  exact ⟨E, ofFull f fun _ _ => ∅, ofFull g fun _ _ => ∅, fun he => h (congrArg full he)⟩

end Silmaril.Proofs.Games.Abstract.StratOps

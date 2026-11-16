module

public import Silmaril.Games.Abstract.HostRun.Defs

/-!
# Running against a relational host (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.HostRun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- The end condition of an observation's run. -/
def OkEnd (R : HostRel E) : End S B ⊕ E.Op → Prop
  | .inl _ => True
  | .inr m => R m .diverge ∨ ∀ ans, ¬ R m ans

theorem okEnd_absurd {R : HostRel E} (hR : R.Functional) {m : E.Op} {n : E.Ar m}
    (h : R m (.answer n)) (hx : OkEnd (S := S) (B := B) R (.inr m)) : False := by
  rcases hx with hx | hx
  · cases hR _ _ _ h hx
  · exact hx _ h

theorem agree_eq {R : HostRel E} (hR : R.Functional) :
    ∀ {cs₁ cs₂ : List (Call E)} {x₁ x₂ : End S B ⊕ E.Op}, PAgree cs₁ x₁ cs₂ x₂ →
      R.Consistent cs₁ → R.Consistent cs₂ → OkEnd R x₁ → OkEnd R x₂ → cs₁ = cs₂ ∧ x₁ = x₂
  | [], [], .inl e₁, .inl e₂, h, _, _, _, _ => ⟨rfl, by rw [show e₁ = e₂ from h]⟩
  | [], [], .inr m₁, .inr m₂, h, _, _, _, _ => ⟨rfl, by rw [show m₁ = m₂ from h]⟩
  | [], [], .inl _, .inr _, h, _, _, _, _ => h.elim
  | [], [], .inr _, .inl _, h, _, _, _, _ => h.elim
  | [], c :: _, .inr m, _, h, _, h₂, hx, _ => by
    have hm : m = c.1 := h
    subst hm
    exact (okEnd_absurd hR (h₂ c (List.mem_cons_self ..)) hx).elim
  | [], _ :: _, .inl _, _, h, _, _, _, _ => h.elim
  | c :: _, [], _, .inr m, h, h₁, _, _, hx => by
    have hm : c.1 = m := h
    subst hm
    exact (okEnd_absurd hR (h₁ c (List.mem_cons_self ..)) hx).elim
  | _ :: _, [], _, .inl _, h, _, _, _, _ => h.elim
  | ⟨m₁, n₁⟩ :: c₁, ⟨m₂, n₂⟩ :: c₂, x₁, x₂, h, h₁, h₂, hx₁, hx₂ => by
    obtain ⟨hm, hk⟩ := h
    subst hm
    have e₁ := h₁ ⟨m₁, n₁⟩ (List.mem_cons_self ..)
    have e₂ := h₂ ⟨m₁, n₂⟩ (List.mem_cons_self ..)
    have hn : n₁ = n₂ := by cases hR _ _ _ e₁ e₂; rfl
    subst hn
    obtain ⟨rfl, rfl⟩ := agree_eq hR (hk HEq.rfl) (fun c hc => h₁ c (List.mem_cons_of_mem _ hc))
      (fun c hc => h₂ c (List.mem_cons_of_mem _ hc)) hx₁ hx₂
    exact ⟨rfl, rfl⟩

theorem run_mem {R : HostRel E} {f : AFun E S A B} {p : Pending E S A} {s : S} {a : A}
    {o : HObs E S B} (h : o ∈ hostObs R f p s a) :
    o.run ∈ runs f p s a ∧ R.Consistent o.run.1 ∧ OkEnd R o.run.2 := by
  rcases h with ⟨cs, e, rfl, h, hc⟩ | ⟨cs, m, rfl, h, hc, hd⟩ | ⟨cs, m, rfl, h, hc, hb⟩
  · exact ⟨.inl ⟨cs, e, rfl, h⟩, hc, trivial⟩
  · exact ⟨.inr ⟨cs, m, rfl, h⟩, hc, .inl hd⟩
  · exact ⟨.inr ⟨cs, m, rfl, h⟩, hc, .inr hb⟩

/-- **A deterministic function against a functional host has at most one
observation.** -/
theorem hostObs_unique {R : HostRel E} (hR : R.Functional) {f : AFun E S A B} {p : Pending E S A}
    (hD : DetP f p) {s : S} {a : A} {o o' : HObs E S B} (h : o ∈ hostObs R f p s a)
    (h' : o' ∈ hostObs R f p s a) : o = o' := by
  obtain ⟨r, c, k⟩ := run_mem h
  obtain ⟨r', c', k'⟩ := run_mem h'
  obtain ⟨e₁, e₂⟩ := agree_eq hR (hD s a _ _ r r') c c' k k'
  rcases h with ⟨cs, e, rfl, -⟩ | ⟨cs, m, rfl, -, -, hd⟩ | ⟨cs, m, rfl, -, -, hb⟩ <;>
    rcases h' with ⟨cs', e', rfl, -⟩ | ⟨cs', m', rfl, -, -, hd'⟩ | ⟨cs', m', rfl, -, -, hb'⟩ <;>
    simp only [HObs.run, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e₁ e₂ <;>
    subst e₁ <;> subst e₂ <;> first | rfl | exact (hb' _ hd).elim | exact (hb _ hd').elim

/-- Against a host function, only finished behaviours are observed: those of
`AFun.under`. -/
theorem hostObs_ofHost (h : Host E) (f : AFun E S A B) (p : Pending E S A) (s : S) (a : A)
    (o : HObs E S B) :
    o ∈ hostObs (HostRel.ofHost h) f p s a ↔ ∃ x ∈ AFun.under h f s a, o = .done x.1 x.2 := by
  have hc : ∀ cs : List (Call E), (HostRel.ofHost h).Consistent cs ↔ AFun.Consistent h cs :=
    fun cs => ⟨fun hc x hx => HostAns.answer.inj (hc x hx),
      fun hc x hx => show HostAns.answer x.2 = .answer (h x.1) by rw [hc x hx]⟩
  constructor
  · rintro (⟨cs, e, rfl, hm, hcs⟩ | ⟨cs, m, rfl, -, -, hd⟩ | ⟨cs, m, rfl, -, -, hb⟩)
    · exact ⟨(cs, e), ⟨hm, (hc cs).mp hcs⟩, rfl⟩
    · cases hd
    · exact (hb _ rfl).elim
  · rintro ⟨⟨cs, e⟩, ⟨hm, hcs⟩, rfl⟩
    exact .inl ⟨cs, e, rfl, hm, (hc cs).mpr hcs⟩

end Silmaril.Proofs.Games.Abstract.HostRun

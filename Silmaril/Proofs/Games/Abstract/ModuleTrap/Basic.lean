module

public import Silmaril.Games.Abstract.ModuleTrap.Defs
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# Closing modules whose trapped calls end the caller (proofs)

* `TrapLast` bookkeeping: appending, consing, a trapped element followed by another is absent;
* `subst_trapLast`, `close_trapAborts`: resolving an open behaviour whose trapped calls end it,
  against a closed module whose trapped import calls end its behaviours, gives a behaviour whose
  trapped import calls end it; hence the closure of such an open module has the property;
* `substPre_noTrap`, `descends_noTrap`, `descPath_noTrap`: a resolved prefix of untrapped calls,
  and the import calls of a descent, contain no trapped import call;
* `closeD_div_noTrap`, `closeDLog_div_noTrap`, `closeInfL_noTrap`: divergent behaviours and
  productive streams contain none.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.ModuleTrap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-! ## `TrapLast` -/

section TrapLast

variable {α : Type u} {P : α → Prop} {Q Q' : Prop} {l l₁ l₂ : List α} {x y : α}

theorem trapLast_nil : TrapLast P Q [] := by
  intro u x v h
  simp at h

theorem trapLast_of_forall (h : ∀ x ∈ l, ¬ P x) : TrapLast P Q l := by
  intro u x v hl hx
  exact absurd hx (h x (by simp [hl]))

theorem TrapLast.forall_not (h : TrapLast P Q l) (hQ : ¬ Q) : ∀ x ∈ l, ¬ P x := by
  intro x hx hp
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hx
  exact hQ (h u x v rfl hp).2

theorem TrapLast.mono (h : TrapLast P Q l) (hQ : Q → Q') : TrapLast P Q' l := by
  intro u x v hl hx
  obtain ⟨h1, h2⟩ := h u x v hl hx
  exact ⟨h1, hQ h2⟩

theorem TrapLast.append_left (h : TrapLast P Q (l₁ ++ y :: l₂)) : ∀ x ∈ l₁, ¬ P x := by
  intro x hx hp
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hx
  have := (h u x (v ++ y :: l₂) (by simp) hp).1
  simp at this

theorem TrapLast.append_right (h : TrapLast P Q (l₁ ++ l₂)) : TrapLast P Q l₂ := by
  intro u x v hl hx
  exact h (l₁ ++ u) x v (by simp [hl]) hx

theorem TrapLast.append (h₁ : ∀ x ∈ l₁, ¬ P x) (h₂ : TrapLast P Q l₂) :
    TrapLast P Q (l₁ ++ l₂) := by
  intro u x v hl hx
  rcases List.append_eq_append_iff.1 hl with ⟨a', rfl, h⟩ | ⟨c', rfl, h⟩
  · exact h₂ a' x v h hx
  · rcases c' with _ | ⟨c, c'⟩
    · exact h₂ [] x v (by simpa using h.symm) hx
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact absurd hx (h₁ _ (by simp))

theorem TrapLast.cons (hx : P x → l = [] ∧ Q) (h : TrapLast P Q l) : TrapLast P Q (x :: l) := by
  intro u y v hl hy
  rcases u with _ | ⟨z, u⟩
  · simp only [List.nil_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact hx hy
  · simp only [List.cons_append, List.cons.injEq] at hl
    exact h u y v hl.2 hy

theorem TrapLast.head (h : TrapLast P Q (x :: l)) (hx : P x) : l = [] ∧ Q :=
  h [] x l rfl hx

theorem TrapLast.tail (h : TrapLast P Q (x :: l)) : TrapLast P Q l :=
  TrapLast.append_right (l₁ := [x]) h

theorem trapLast_concat (h₁ : ∀ x ∈ l, ¬ P x) (h₂ : P y → Q) : TrapLast P Q (l ++ [y]) :=
  TrapLast.append h₁ (TrapLast.cons (fun h => ⟨rfl, h₂ h⟩) trapLast_nil)

theorem trapLast_singleton (h : P y → Q) : TrapLast P Q [y] :=
  TrapLast.cons (fun h' => ⟨rfl, h h'⟩) trapLast_nil

end TrapLast

/-! ## Resolution -/

variable {T : (m : sh.E.Op) → sh.E.Ar m → Prop} {TE : (f : sh.F) → End sh.S (sh.B f) → Prop}

/-- **Resolving a trap-aborting open behaviour against a trap-aborting closed module.** -/
theorem subst_trapLast {c : sh.ClosedMod} (hc : ClosedTrapAborts T TE c)
    (hdiv : ∀ g, ¬ TE g .div) {R : Type u} {TR : End sh.S R → Prop}
    (hTR : TR .trap) {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R}
    {y : CallBeh sh.E sh.S R} (hs : Subst c x e y) (hx : TrapLast (TrapCall T TE) (TR e) x) :
    TrapLast (fun x : Call sh.E => T x.1 x.2) (TR y.2) y.1 := by
  induction hs with
  | nil e => exact trapLast_nil
  | @ext m n rest e y hsub ih =>
    refine TrapLast.cons (fun hT => ?_) (ih (TrapLast.tail hx))
    obtain ⟨rfl, hQ⟩ := TrapLast.head hx hT
    cases hsub
    exact ⟨rfl, hQ⟩
  | @int g a s b s' rest e c₁ y hcb hsub ih =>
    have h₁ := hc g s a _ hcb
    by_cases hb : TE g (.ret b s')
    · obtain ⟨rfl, hQ⟩ := TrapLast.head hx hb
      cases hsub
      simpa using TrapLast.mono h₁ fun _ => hQ
    · exact TrapLast.append (TrapLast.forall_not h₁ hb) (ih (TrapLast.tail hx))
  | intTrap hcb => exact TrapLast.mono (hc _ _ _ _ hcb) fun _ => hTR
  | intDiv hcb => exact trapLast_of_forall (TrapLast.forall_not (hc _ _ _ _ hcb) (hdiv _))

/-- **The closure of a trap-aborting open module is trap-aborting.** -/
theorem close_trapAborts {m : sh.OpenMod} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div) : ClosedTrapAborts T TE (close m) := by
  let c : sh.ClosedMod := fun f _ _ =>
    {y | TrapLast (fun x : Call sh.E => T x.1 x.2) (TE f y.2) y.1}
  have hc : ClosedTrapAborts T TE c := fun _ _ _ _ hy => hy
  have hle : resolve m c ≤ c := by
    rintro f s a y ⟨x, hx, hs⟩
    exact subst_trapLast hc hdiv (htrap f) hs (hm f s a x hx)
  intro f s a y hy
  exact OrderHom.lfp_le _ hle f s a hy

/-! ## Prefixes, descents and divergence -/

theorem substPre_noTrap {c : sh.ClosedMod} (hc : ClosedTrapAborts T TE c)
    {u : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (h : SubstPre c u q)
    (hu : ∀ x ∈ u, ¬ TrapCall T TE x) : ∀ x ∈ q, ¬ T x.1 x.2 := by
  induction h with
  | nil => simp
  | @ext m n rest q _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hu ⟨.inl m, n⟩ (List.Mem.head _)
    · exact ih (fun x hx => hu x (List.mem_cons_of_mem _ hx)) x hx
  | @int g a s b s' rest c₁ q hcb _ ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact TrapLast.forall_not (hc _ _ _ _ hcb) (hu ⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ (List.Mem.head _)) x hx
    · exact ih (fun x hx => hu x (List.mem_cons_of_mem _ hx)) x hx

theorem descends_noTrap {m : sh.OpenMod} {c : sh.ClosedMod} (hm : OpenTrapAborts T TE m)
    (hc : ClosedTrapAborts T TE c) {x y : sh.self.Op} {q : List (Call sh.E)}
    (h : Descends m c x q y) : ∀ e ∈ q, ¬ T e.1 e.2 := by
  obtain ⟨z, hz, u, ans, rest, hzu, hpre⟩ := h
  have := hm _ _ _ _ hz
  rw [hzu] at this
  exact substPre_noTrap hc hpre (TrapLast.append_left this)

theorem descPath_noTrap {m : sh.OpenMod} {c : sh.ClosedMod} (hm : OpenTrapAborts T TE m)
    (hc : ClosedTrapAborts T TE c) {x z : sh.self.Op} {qs : List (Call sh.E)}
    (h : DescPath m c x qs z) : ∀ e ∈ qs, ¬ T e.1 e.2 := by
  induction h with
  | refl => simp
  | step hd _ ih =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact descends_noTrap hm hc hd e he
    · exact ih e he

theorem closeD_div_noTrap {m : sh.OpenMod} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div) {f : sh.F} {s : sh.S} {a : sh.A f}
    {y : CallBeh sh.E sh.S (sh.B f)} (hy : y ∈ closeD m f s a) (hd : y.2 = .div) :
    ∀ e ∈ y.1, ¬ T e.1 e.2 := by
  have hc := close_trapAborts hm htrap hdiv
  rcases hy with hy | ⟨-, g, q, N, -, hdesc, -, hqs⟩
  · exact TrapLast.forall_not (hc _ _ _ _ hy) (by rw [hd]; exact hdiv f)
  · intro e he
    rw [hqs, List.mem_flatMap] at he
    obtain ⟨n, -, he⟩ := he
    exact descends_noTrap hm hc (hdesc n) e he

theorem closeDLog_div_noTrap {m : sh.OpenMod}
    {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div)
    (hL : ∀ z u, LDL z u → ∀ x ∈ u, ¬ TrapCall T TE x) {f : sh.F} {s : sh.S} {a : sh.A f}
    {y : CallBeh sh.E sh.S (sh.B f)} (hy : y ∈ closeDLog m LDL f s a) (hd : y.2 = .div) :
    ∀ e ∈ y.1, ¬ T e.1 e.2 := by
  have hc := close_trapAborts hm htrap hdiv
  rcases hy with hy | ⟨-, z, qs, u, q, hpath, hLz, hpre, hy1⟩
  · exact closeD_div_noTrap hm htrap hdiv hy hd
  · intro e he
    rw [hy1] at he
    rcases List.mem_append.1 he with he | he
    · exact descPath_noTrap hm hc hpath e he
    · exact substPre_noTrap hc hpre (hL z u hLz) e he

/-! ## Productive streams -/

theorem streamConcat_mem {α : Type u} {l : Nat → List α} {ω : Nat → α}
    (h : StreamConcat l ω) (k : Nat) : ∃ i, ω k ∈ l i := by
  obtain ⟨n, hn⟩ := h.2 (k + 1)
  have hk : k < ((List.range n).flatMap l).length := by omega
  have := h.1 n k hk
  have hm : ω k ∈ (List.range n).flatMap l := by
    rw [this]
    exact List.getElem_mem hk
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hm
  exact ⟨i, hi⟩

theorem res1_noTrap {c : sh.ClosedMod} (hc : ClosedTrapAborts T TE c)
    {x : Call (sh.E ⊕ₛ sh.self)} {l : List (Call sh.E)} (h : Res1 c x l)
    (hx : ¬ TrapCall T TE x) : ∀ e ∈ l, ¬ T e.1 e.2 := by
  cases h with
  | ext =>
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact hx
  | int hcb => exact TrapLast.forall_not (hc _ _ _ _ hcb) hx

theorem closeInfL_noTrap {m : sh.OpenMod} {mi : OpenInf sh} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div)
    (hmi : ∀ f s a ν, ν ∈ mi f s a → ∀ i, ¬ TrapCall T TE (ν i)) {f : sh.F} {s : sh.S}
    {a : sh.A f} {ω : Nat → Call sh.E} (hω : ω ∈ closeInfL m mi f s a) (k : Nat) :
    ¬ T (ω k).1 (ω k).2 := by
  have hc := close_trapAborts hm htrap hdiv
  rcases hω with ⟨g, q, -, hdesc, hpre, hunb⟩ | ⟨z, qs, ν, ω', hpath, hν, ⟨l, hres, hcat⟩, rfl⟩
  · obtain ⟨i, hi⟩ := streamConcat_mem (l := q) ⟨hpre, hunb⟩ k
    exact descends_noTrap hm hc (hdesc i) _ hi
  · by_cases hk : k < qs.length
    · rw [streamAppend_lt hk]
      exact descPath_noTrap hm hc hpath _ (List.getElem_mem hk)
    · rw [streamAppend_ge (Nat.not_lt.1 hk)]
      obtain ⟨i, hi⟩ := streamConcat_mem hcat (k - qs.length)
      exact res1_noTrap hc (hres i) (hmi _ _ _ _ hν i) _ hi
end Silmaril.Proofs.Games.Abstract.ModuleTrap

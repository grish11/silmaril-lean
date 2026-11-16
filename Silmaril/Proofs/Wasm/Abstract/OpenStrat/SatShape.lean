module

public import Silmaril.Games.Abstract.Module.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms
public import Silmaril.Games.Abstract.ModuleDLog.Defs
public import Silmaril.Games.Abstract.CloseReach.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# Call prefixes of closures are pending calls (proofs, any shape)

A predicate `P x c e` ("after the import calls `c`, the call `x` of the module has the pending
import call `e`") is closed under the calls of an open log `u` of `x` (`LogOk m P x u`) when an
import call of `u` after the prefix `u₁` is pending after the resolution of `u₁`, and an internal
call `y` of `u` after `u₁` passes the pending calls of `y` to `x`, behind the resolution of `u₁`.

If every open behaviour's log is `LogOk`, every call prefix forced by the closure is pending:

* `close_pend`: in a behaviour of `close m`, the import calls before an import call (least-fixpoint
  induction, the call split by `subst_split`);
* `logOk_pend`: in the resolution of a `LogOk` log;
* `descPath_pend`: along a descent path; `descPath_trans`: a descent path passes pending calls;
* `closeDLog_pend`: in a behaviour of `closeDLog m LDL`, when the logs of `LDL` are `LogOk`;
* `closeInfL_pend`: in a stream of `closeInfL m mi`, when the prefixes of the open streams of `mi`
  are `LogOk`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.OpenStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

/-! ## Lists and streams -/

theorem split_app {α : Type u} {a b pre post : List α} {x : α} (h : a ++ b = pre ++ x :: post) :
    (∃ post', a = pre ++ x :: post') ∨ ∃ pre', pre = a ++ pre' ∧ b = pre' ++ x :: post := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, hb⟩ | ⟨c', rfl, hc⟩
  · exact .inr ⟨a', rfl, hb⟩
  · rcases c' with _ | ⟨y, c'⟩
    · exact .inr ⟨[], by simp, by simpa using hc.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact .inl ⟨c', rfl⟩

theorem length_streamTake {α : Type u} (ω : Nat → α) (k : Nat) : (streamTake ω k).length = k :=
  List.length_ofFn

theorem getElem_streamTake {α : Type u} (ω : Nat → α) (k i : Nat)
    (h : i < (streamTake ω k).length) : (streamTake ω k)[i] = ω i :=
  List.getElem_ofFn ..

theorem streamTake_succ {α : Type u} (ω : Nat → α) (k : Nat) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  apply List.ext_getElem (by simp [length_streamTake])
  intro i h₁ h₂
  rw [getElem_streamTake, List.getElem_append]
  split
  · rw [getElem_streamTake]
  · rename_i hi
    have : i = k := by
      simp only [length_streamTake, List.length_append, List.length_singleton] at h₁ h₂ hi
      omega
    subst this
    simp [length_streamTake]

theorem streamTake_map {α β : Type u} (f : α → β) (ω : Nat → α) (k : Nat) :
    streamTake (fun i => f (ω i)) k = (streamTake ω k).map f := by
  simp [streamTake, List.map_ofFn]
  rfl

/-- A list a stream starts with, split at position `k`. -/
theorem prefix_split {α : Type u} {L : List α} {ω : Nat → α} (h : StreamPrefix L ω) {k : Nat}
    (hk : k < L.length) : L = streamTake ω k ++ ω k :: L.drop (k + 1) := by
  have htk : L.take k = streamTake ω k := by
    apply List.ext_getElem (by simp [length_streamTake]; omega)
    intro i h₁ h₂
    rw [getElem_streamTake, List.getElem_take, h i (by simp at h₁; omega)]
  rw [← htk, h k hk, List.getElem_cons_drop, List.take_append_drop]

/-- A split of a prefix of a stream is a prefix and the next element. -/
theorem streamTake_split {α : Type u} {ω : Nat → α} {n : Nat} {u₁ u₂ : List α} {x : α}
    (h : streamTake ω n = u₁ ++ x :: u₂) : u₁ = streamTake ω u₁.length ∧ x = ω u₁.length := by
  have hl : u₁.length < n := by
    have := congrArg List.length h
    simp [length_streamTake] at this
    omega
  have hp : StreamPrefix (streamTake ω n) ω := fun i hi => (getElem_streamTake ω n i hi).symm
  have := prefix_split hp (k := u₁.length) (by simp [length_streamTake]; omega)
  rw [h] at this
  simp only [List.drop_append] at this
  have h₂ := List.append_inj this (by simp [length_streamTake])
  obtain ⟨h₁, h₃⟩ := h₂
  simp only [List.cons.injEq] at h₃
  exact ⟨h₁, h₃.1⟩

theorem streamAppend_cases {α : Type u} (l : List α) (ω : Nat → α) (k : Nat) :
    (∃ w, l = streamTake (l ++ω ω) k ++ (l ++ω ω) k :: w) ∨
      ∃ j, streamTake (l ++ω ω) k = l ++ streamTake ω j ∧ (l ++ω ω) k = ω j := by
  by_cases hk : k < l.length
  · exact .inl ⟨_, prefix_split (fun i hi => streamAppend_lt hi) hk⟩
  · refine .inr ⟨k - l.length, ?_, streamAppend_ge (by omega)⟩
    apply List.ext_getElem (by simp [length_streamTake]; omega)
    intro i h₁ h₂
    rw [getElem_streamTake, List.getElem_append]
    split
    · exact streamAppend_lt _
    · rw [getElem_streamTake, streamAppend_ge (by omega)]

/-- An element of a concatenation of lists lies in one of them. -/
theorem flatMap_split {α : Type u} (l : Nat → List α) :
    ∀ (n : Nat) {pre w : List α} {x : α}, (List.range n).flatMap l = pre ++ x :: w →
      ∃ j pre' w', l j = pre' ++ x :: w' ∧ pre = (List.range j).flatMap l ++ pre' := by
  intro n
  induction n with
  | zero => intro pre w x h; simp at h
  | succ n ih =>
    intro pre w x h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at h
    rcases split_app h with ⟨w', h₁⟩ | ⟨pre', rfl, h₂⟩
    · exact ih h₁
    · exact ⟨n, pre', w, h₂, rfl⟩

/-! ## Resolution -/

variable {sh : Shape.{u}}

theorem substPre_subst {c : sh.ClosedMod} {R : Type u} {x : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} (h : SubstPre c x q) (e : End sh.S R) : Subst c x e (q, e) := by
  induction h with
  | nil => exact .nil e
  | @ext _ _ _ q _ ih => exact Subst.ext (y := (q, e)) ih
  | @int _ _ _ _ _ _ _ q hm _ ih => exact Subst.int (y := (q, e)) hm ih

theorem substPre_append {c : sh.ClosedMod} {u v : List (Call (sh.E ⊕ₛ sh.self))}
    {q r : List (Call sh.E)} (hu : SubstPre c u q) (hv : SubstPre c v r) :
    SubstPre c (u ++ v) (q ++ r) := by
  induction hu with
  | nil => exact hv
  | ext _ ih => exact .ext ih
  | int hm _ ih => rw [List.cons_append, List.append_assoc]; exact .int hm ih

theorem substPre_streamTake {c : sh.ClosedMod} {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    {l : Nat → List (Call sh.E)} (h : ∀ i, Res1 c (ν i) (l i)) :
    ∀ n, SubstPre c (streamTake ν n) ((List.range n).flatMap l) := by
  intro n
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [streamTake_succ, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine substPre_append ih ?_
    have hn := h n
    generalize ν n = z at hn ⊢
    generalize l n = L at hn ⊢
    cases hn with
    | ext => exact .ext .nil
    | int hm => simpa using SubstPre.int hm .nil

/-- **An import call in a resolution comes from the open log**: an import call of the log, or a
call inside the behaviour of a resolved callee. -/
theorem subst_split {c : sh.ClosedMod} {R : Type u} {x : List (Call (sh.E ⊕ₛ sh.self))}
    {e₀ : End sh.S R} {y : CallBeh sh.E sh.S R} (h : Subst c x e₀ y) :
    ∀ {pre post : List (Call sh.E)} {ev : Call sh.E}, y.1 = pre ++ ev :: post →
      ∃ (u₁ : List (Call (sh.E ⊕ₛ sh.self))) (cl : Call (sh.E ⊕ₛ sh.self))
        (u₂ : List (Call (sh.E ⊕ₛ sh.self))) (q₁ : List (Call sh.E)),
        x = u₁ ++ cl :: u₂ ∧ SubstPre c u₁ q₁ ∧
        ((∃ n : sh.E.Ar ev.1, cl = ⟨.inl ev.1, n⟩) ∧ pre = q₁ ∨
          ∃ (g : sh.F) (a : sh.A g) (s : sh.S) (ans : sh.B g × sh.S) (c₁ : List (Call sh.E))
            (r : End sh.S (sh.B g)) (pre' w : List (Call sh.E)),
            cl = ⟨.inr ⟨g, (a, s)⟩, ans⟩ ∧ (c₁, r) ∈ c g s a ∧ c₁ = pre' ++ ev :: w ∧
              pre = q₁ ++ pre') := by
  induction h with
  | nil => intro pre post ev hy; simp at hy
  | @ext m n rest e y _ ih =>
    intro pre post ev hy
    rcases pre with _ | ⟨p, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      exact ⟨[], _, rest, [], rfl, .nil, .inl ⟨⟨n, rfl⟩, rfl⟩⟩
    · simp only [List.cons_append, List.cons.injEq] at hy
      obtain ⟨rfl, hy⟩ := hy
      obtain ⟨u₁, cl, u₂, q₁, rfl, hq, hc⟩ := ih hy
      refine ⟨⟨.inl m, n⟩ :: u₁, cl, u₂, ⟨m, n⟩ :: q₁, rfl, .ext hq, ?_⟩
      rcases hc with ⟨hn, rfl⟩ | ⟨g, a, s, ans, c₁, r, pre', w, h₁, h₂, h₃, rfl⟩
      · exact .inl ⟨hn, rfl⟩
      · exact .inr ⟨g, a, s, ans, c₁, r, pre', w, h₁, h₂, h₃, rfl⟩
  | @int g a s b s' rest e c₁ y hm _ ih =>
    intro pre post ev hy
    rcases split_app hy with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · exact ⟨[], _, rest, [], rfl, .nil, .inr ⟨g, a, s, (b, s'), c₁, _, pre, w, rfl, hm, h₁, rfl⟩⟩
    · obtain ⟨u₁, cl, u₂, q₁, rfl, hq, hc⟩ := ih h₂
      refine ⟨⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ :: u₁, cl, u₂, c₁ ++ q₁, rfl, .int hm hq, ?_⟩
      rcases hc with ⟨hn, rfl⟩ | ⟨g', a', t, ans, c₂, r, pre'', w, k₁, k₂, k₃, rfl⟩
      · exact .inl ⟨hn, rfl⟩
      · exact .inr ⟨g', a', t, ans, c₂, r, pre'', w, k₁, k₂, k₃, by simp⟩
  | @intTrap g a s ans rest e c₁ hm =>
    intro pre post ev hy
    exact ⟨[], _, rest, [], rfl, .nil, .inr ⟨g, a, s, ans, c₁, _, pre, post, rfl, hm, hy, rfl⟩⟩
  | @intDiv g a s ans rest e c₁ hm =>
    intro pre post ev hy
    exact ⟨[], _, rest, [], rfl, .nil, .inr ⟨g, a, s, ans, c₁, _, pre, post, rfl, hm, hy, rfl⟩⟩

/-! ## Pending calls through a closure -/

variable (m : sh.OpenMod) (P : sh.self.Op → List (Call sh.E) → sh.E.Op → Prop)

/-- **The calls of the open log `u` of `x` pass pending calls**: after the prefix `u₁` resolved to
`q`, an import call is pending, and the pending calls of an internal call are pending calls of
`x` behind `q`. -/
def LogOk (x : sh.self.Op) (u : List (Call (sh.E ⊕ₛ sh.self))) : Prop :=
  ∀ (u₁ : List (Call (sh.E ⊕ₛ sh.self))) (cl : Call (sh.E ⊕ₛ sh.self))
    (u₂ : List (Call (sh.E ⊕ₛ sh.self))) (q : List (Call sh.E)),
    u = u₁ ++ cl :: u₂ → SubstPre (close m) u₁ q →
    (∀ (e : sh.E.Op) (n : sh.E.Ar e), cl = ⟨.inl e, n⟩ → P x q e) ∧
    (∀ (y : sh.self.Op) (ans : sh.self.Ar y), cl = ⟨.inr y, ans⟩ →
      ∀ c e, P y c e → P x (q ++ c) e)

/-- Every open behaviour's log passes pending calls. -/
def OpenOk : Prop := ∀ (x : sh.self.Op) z, z ∈ m x.1 x.2.2 x.2.1 → LogOk m P x z.1

variable {m P}

theorem logOk_prefix {x : sh.self.Op} {u v : List (Call (sh.E ⊕ₛ sh.self))}
    (h : LogOk m P x (u ++ v)) : LogOk m P x u :=
  fun u₁ cl u₂ q hu hq => h u₁ cl (u₂ ++ v) q (by simp [hu]) hq

/-- The prefixes of a stream whose every call passes pending calls. -/
theorem logOk_streamTake {x : sh.self.Op} {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    (h : ∀ k q, SubstPre (close m) (streamTake ν k) q →
      (∀ (e : sh.E.Op) (n : sh.E.Ar e), ν k = ⟨.inl e, n⟩ → P x q e) ∧
      (∀ (y : sh.self.Op) (ans : sh.self.Ar y), ν k = ⟨.inr y, ans⟩ →
        ∀ c e, P y c e → P x (q ++ c) e)) (n : Nat) : LogOk m P x (streamTake ν n) := by
  intro u₁ cl u₂ q hu hq
  obtain ⟨h₁, rfl⟩ := streamTake_split hu
  rw [h₁] at hq
  exact h _ q hq

/-- A `LogOk` log resolved through a module whose behaviours pass pending calls. -/
theorem logOk_subst {c : sh.ClosedMod} (hc : c ≤ close m)
    (hcp : ∀ (g : sh.F) (s : sh.S) (a : sh.A g) (c₁ : List (Call sh.E)) (r : End sh.S (sh.B g))
      (pre : List (Call sh.E)) (ev : Call sh.E) (w : List (Call sh.E)),
      (c₁, r) ∈ c g s a → c₁ = pre ++ ev :: w → P ⟨g, (a, s)⟩ pre ev.1)
    {x : sh.self.Op} {u : List (Call (sh.E ⊕ₛ sh.self))} (hu : LogOk m P x u) {R : Type u}
    {e₀ : End sh.S R} {y : CallBeh sh.E sh.S R} (hs : Subst c u e₀ y)
    {pre post : List (Call sh.E)} {ev : Call sh.E} (hy : y.1 = pre ++ ev :: post) :
    P x pre ev.1 := by
  obtain ⟨u₁, cl, u₂, q₁, rfl, hq, hcl⟩ := subst_split hs hy
  have hu' := hu u₁ cl u₂ q₁ rfl (hq.mono hc)
  rcases hcl with ⟨⟨n, rfl⟩, rfl⟩ | ⟨g, a, s, ans, c₁, r, pre', w, rfl, hm, h₁, rfl⟩
  · exact hu'.1 _ n rfl
  · exact hu'.2 ⟨g, (a, s)⟩ ans rfl pre' ev.1 (hcp g s a c₁ r pre' ev w hm h₁)

/-- The behaviours of the closure whose import calls are preceded by pending calls. -/
def PendC (m : sh.OpenMod) (P : sh.self.Op → List (Call sh.E) → sh.E.Op → Prop) :
    sh.ClosedMod := fun f s a =>
  {y | y ∈ close m f s a ∧ ∀ pre ev post, y.1 = pre ++ ev :: post → P ⟨f, (a, s)⟩ pre ev.1}

theorem close_le_pendC (hm : OpenOk m P) : close m ≤ PendC m P := by
  refine OrderHom.lfp_le _ ?_
  rintro f s a y ⟨z, hz, hS⟩
  have hle : PendC m P ≤ close m := fun _ _ _ _ h => h.1
  refine ⟨?_, fun pre ev post hy => ?_⟩
  · rw [← resolve_close m]
    exact ⟨z, hz, hS.mono hle⟩
  · exact logOk_subst hle (fun g s a c₁ r pre ev w hm h => hm.2 pre ev w h)
      (hm ⟨f, (a, s)⟩ z hz) hS hy

/-- **In a behaviour of the closure, the import calls before an import call are pending.** -/
theorem close_pend (hm : OpenOk m P) {x : sh.self.Op} {pre post : List (Call sh.E)}
    {ev : Call sh.E} {r : End sh.S (sh.B x.1)}
    (h : (pre ++ ev :: post, r) ∈ close m x.1 x.2.2 x.2.1) : P x pre ev.1 :=
  (close_le_pendC hm _ _ _ h).2 pre ev post rfl

/-- **In the resolution of a `LogOk` log, the import calls before an import call are
pending.** -/
theorem logOk_pend (hm : OpenOk m P) {x : sh.self.Op} {u : List (Call (sh.E ⊕ₛ sh.self))}
    (hu : LogOk m P x u) {q : List (Call sh.E)} (hq : SubstPre (close m) u q)
    {pre post : List (Call sh.E)} {ev : Call sh.E} (he : q = pre ++ ev :: post) :
    P x pre ev.1 :=
  logOk_subst le_rfl (fun g s a _ _ _ _ _ hc h => close_pend (x := ⟨g, (a, s)⟩) hm (h ▸ hc)) hu
    (substPre_subst hq (End.trap : End sh.S PUnit)) he

/-- A descent passes pending calls. -/
theorem descends_trans (hm : OpenOk m P) {x y : sh.self.Op} {q : List (Call sh.E)}
    (hd : Descends m (close m) x q y) {c : List (Call sh.E)} {e : sh.E.Op} (h : P y c e) :
    P x (q ++ c) e := by
  obtain ⟨z, hz, u, ans, rest, hu, hq⟩ := hd
  exact (hm x z hz u _ rest q hu hq).2 y ans rfl c e h

/-- **A descent path passes pending calls.** -/
theorem descPath_trans (hm : OpenOk m P) {x z : sh.self.Op} {qs : List (Call sh.E)}
    (hp : DescPath m (close m) x qs z) {c : List (Call sh.E)} {e : sh.E.Op} (h : P z c e) :
    P x (qs ++ c) e := by
  induction hp with
  | refl => exact h
  | step hd _ ih => simpa [List.append_assoc] using descends_trans hm hd (ih h)

/-- **Along a descent path, the import calls before an import call are pending.** -/
theorem descPath_pend (hm : OpenOk m P) {x z : sh.self.Op} {qs : List (Call sh.E)}
    (hp : DescPath m (close m) x qs z) :
    ∀ {pre post : List (Call sh.E)} {ev : Call sh.E}, qs = pre ++ ev :: post → P x pre ev.1 := by
  induction hp with
  | refl => intro pre post ev h; simp at h
  | step hd _ ih =>
    intro pre post ev h
    rcases split_app h with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · obtain ⟨z, hz, u, ans, rest, hu, hq⟩ := hd
      exact logOk_pend hm (logOk_prefix (v := _ :: rest) (hu ▸ hm _ z hz)) hq h₁
    · exact descends_trans hm hd (ih h₂)

theorem descPath_snoc {c : sh.ClosedMod} {x y z : sh.self.Op} {qs q : List (Call sh.E)}
    (h : DescPath m c x qs y) (hd : Descends m c y q z) : DescPath m c x (qs ++ q) z := by
  induction h with
  | refl => simpa using DescPath.step hd (.refl _)
  | step h' _ ih => simpa [List.append_assoc] using DescPath.step h' (ih hd)

theorem descPath_chain {c : sh.ClosedMod} (g : Nat → sh.self.Op) (q : Nat → List (Call sh.E))
    (hd : ∀ n, Descends m c (g n) (q n) (g (n + 1))) :
    ∀ N, DescPath m c (g 0) ((List.range N).flatMap q) (g N) := by
  intro N
  induction N with
  | zero => exact .refl _
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    simpa using descPath_snoc ih (hd N)

/-- **In a behaviour of `closeDLog`, the import calls before an import call are pending**, when
the logs of the logged local divergence pass pending calls. -/
theorem closeDLog_pend (hm : OpenOk m P)
    {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop}
    (hL : ∀ z u, LDL z u → LogOk m P z u) {x : sh.self.Op} {y : CallBeh sh.E sh.S (sh.B x.1)}
    (h : y ∈ closeDLog m LDL x.1 x.2.2 x.2.1) {pre post : List (Call sh.E)} {ev : Call sh.E}
    (hy : y.1 = pre ++ ev :: post) : P x pre ev.1 := by
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at hy
  subst hy
  rcases h with (hc | ⟨-, g, q, N, hg, hD, -, hqs⟩) | ⟨-, z, qs, u, q, hp, hl, hsub, hq⟩
  · exact close_pend hm hc
  · have := descPath_chain g q hD N
    rw [hg] at this
    exact descPath_pend hm this hqs.symm
  · rcases split_app hq.symm with ⟨w, h₁⟩ | ⟨pre', rfl, h₂⟩
    · exact descPath_pend hm hp h₁
    · exact descPath_trans hm hp (logOk_pend hm (hL z u hl) hsub h₂)

/-- **In a stream of `closeInfL`, every prefix before a call is pending**, when the prefixes of
the open streams pass pending calls. -/
theorem closeInfL_pend (hm : OpenOk m P) {mi : OpenInf sh}
    (hI : ∀ (z : sh.self.Op) ν, ν ∈ mi z.1 z.2.2 z.2.1 → ∀ n, LogOk m P z (streamTake ν n))
    {x : sh.self.Op} {ω : Nat → Call sh.E} (h : ω ∈ closeInfL m mi x.1 x.2.2 x.2.1) (k : Nat) :
    P x (streamTake ω k) (ω k).1 := by
  rcases h with ⟨g, q, hg, hD, hpre, hun⟩ | ⟨z, qs, ν, ω', hp, hν, ⟨l, hres, hpre, hun⟩, rfl⟩
  · obtain ⟨n, hn⟩ := hun (k + 1)
    have := descPath_chain g q hD n
    rw [hg] at this
    exact descPath_pend hm this (prefix_split (hpre n) (by omega))
  · rcases streamAppend_cases qs ω' k with ⟨w, h₁⟩ | ⟨j, h₁, h₂⟩
    · exact descPath_pend hm hp h₁
    · rw [h₁, h₂]
      obtain ⟨n, hn⟩ := hun (j + 1)
      exact descPath_trans hm hp (logOk_pend hm (hI z ν hν n) (substPre_streamTake hres n)
        (prefix_split (hpre n) (by omega)))

end Silmaril.Proofs.Wasm.Abstract.OpenStrat

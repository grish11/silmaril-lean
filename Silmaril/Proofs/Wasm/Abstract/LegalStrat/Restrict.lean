module

public import Silmaril.Wasm.Abstract.BodyStrat.Thms
public import Silmaril.Semantics.ITree.Thms

/-!
# Restriction of a body's triple to legally answered logs (proofs)

For an interaction-tree body and a legality predicate `L` on the lifted answers, the triple of the
body restricted to legally answered logs (`StratLegal.restrict L (toTriple f)`) is determined by
the finished paths and pending calls at legal logs (`restrict_eq_iff`):

* a silent divergence at a legal log is what remains when neither a value nor a pending call is
  there, at a node reached through legal answers (`path_div_of`);
* an infinite productive stream with legal answers is a limit of legal pending prefixes
  (`mem_restrict_inf_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.LegalStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.BodyStrat Silmaril.Elgot.ITree
open Silmaril.Games.Abstract.StratLegal (legalSig restrict)
open Silmaril.Games.Abstract.StratLegal renaming liftCall → liftCallL
open Silmaril.Wasm.Abstract.BodyTrace renaming liftCall → liftCallB

universe u v w

/-! ## Interaction trees -/

section
variable {E : Sig.{u}} {Y : Type (u + 1)}

theorem vis_heq {R R' : Type u} {e : SigEv E R} {e' : SigEv E R'}
    {k : R → Tree (SigEv E) Y} {k' : R' → Tree (SigEv E) Y} (h : vis e k = vis e' k') :
    R = R' ∧ HEq e e' ∧ HEq k k' := by
  have := congrArg out h
  simp only [out_vis, Part.some_inj, Visible.vis.injEq] at this
  exact this

theorem call_answer_inj {m : E.Op} {R : Type u} (h : E.Ar m = R) {n n' : R}
    (hc : (⟨m, cast h.symm n⟩ : Call E) = ⟨m, cast h.symm n'⟩) : n = n' := by
  have := congrArg (cast h) (eq_of_heq (Sigma.mk.inj_iff.1 hc).2)
  simpa using this

theorem path_vis_cons {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y} {r : R}
    {cs : List (Call E)} {x : PathEnd Y} :
    Path (vis e k) (⟨e.1, cast e.2.symm r⟩ :: cs) x ↔ Path (k r) cs x := by
  refine ⟨fun h => ?_, fun h => .vis rfl h⟩
  obtain ⟨n, cs', hc, hp⟩ := path_vis_inv h
  simp only [List.cons.injEq] at hc
  obtain ⟨hc, rfl⟩ := hc
  obtain rfl := call_answer_inj e.2 hc
  exact hp

theorem pend_vis_inv {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y}
    {cs : List (Call E)} {m : E.Op} (h : Pend (vis e k) cs m) :
    (cs = [] ∧ m = e.1) ∨ ∃ n cs', cs = ⟨e.1, cast e.2.symm n⟩ :: cs' ∧ Pend (k n) cs' m := by
  cases h with
  | here h =>
    obtain ⟨rfl, he, -⟩ := vis_heq h
    obtain rfl := eq_of_heq he
    exact .inl ⟨rfl, rfl⟩
  | vis h hp =>
    obtain ⟨rfl, he, hk⟩ := vis_heq h
    obtain rfl := eq_of_heq he
    obtain rfl := eq_of_heq hk
    exact .inr ⟨_, _, rfl, hp⟩

theorem pend_vis_cons {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y} {r : R}
    {cs : List (Call E)} {m : E.Op} :
    Pend (vis e k) (⟨e.1, cast e.2.symm r⟩ :: cs) m ↔ Pend (k r) cs m := by
  refine ⟨fun h => ?_, fun h => .vis rfl h⟩
  rcases pend_vis_inv h with ⟨h, -⟩ | ⟨n, cs', hc, hp⟩
  · cases h
  · simp only [List.cons.injEq] at hc
    obtain ⟨hc, rfl⟩ := hc
    obtain rfl := call_answer_inj e.2 hc
    exact hp

theorem not_pend_ret {a : Y} {cs : List (Call E)} {m : E.Op} : ¬ Pend (ret a) cs m := by
  intro h
  cases h with
  | here h => exact ret_ne_vis _ _ _ h
  | vis h _ => exact ret_ne_vis _ _ _ h

theorem not_pend_diverge {cs : List (Call E)} {m : E.Op} :
    ¬ Pend (diverge : Tree (SigEv E) Y) cs m := by
  intro h
  cases h with
  | here h => exact vis_ne_diverge _ _ h.symm
  | vis h _ => exact vis_ne_diverge _ _ h.symm

theorem not_path_diverge_val {cs : List (Call E)} {a : Y} :
    ¬ Path (diverge : Tree (SigEv E) Y) cs (.val a) := by
  intro h
  cases h with
  | ret h => exact ret_ne_diverge _ h.symm
  | vis h _ => exact vis_ne_diverge _ _ h.symm

/-- **Silent divergence at a legal log is determined** by the values and pending calls at legal
logs: the node reached is neither a return nor a call. -/
theorem path_div_of {P : Call E → Prop} :
    ∀ (cs : List (Call E)) (t t' : Tree (SigEv E) Y), (∀ c ∈ cs, P c) →
      (∀ cs', (∀ c ∈ cs', P c) →
        ((∃ a, Path t cs' (.val a)) ↔ ∃ a, Path t' cs' (.val a)) ∧
          ∀ m, Pend t cs' m ↔ Pend t' cs' m) →
      Path t cs .div → Path t' cs .div
  | [], t, t', _, h, hp => by
    have ht : t = diverge := by cases hp with | div h => exact h
    subst ht
    rcases cases_visible t' with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · exact .div rfl
    · obtain ⟨a', ha'⟩ := ((h [] (by simp)).1).2 ⟨a, .ret rfl⟩
      exact absurd ha' not_path_diverge_val
    · exact absurd (((h [] (by simp)).2 e.1).2 (.here rfl)) not_pend_diverge
  | c :: cs, t, t', hl, h, hp => by
    cases hp with
    | @vis t₀ R e k n cs₀ r₀ ht hp' =>
      subst ht
      obtain ⟨m, hm⟩ := e
      subst hm
      have hq := ((h [] (by simp)).2 m).1 (.here rfl)
      rcases cases_visible t' with rfl | ⟨a, rfl⟩ | ⟨R', ⟨m', hm'⟩, k', rfl⟩
      · exact absurd hq not_pend_diverge
      · exact absurd hq not_pend_ret
      · subst hm'
        rcases pend_vis_inv hq with ⟨-, hmm⟩ | ⟨_, _, hc, -⟩
        · change m = m' at hmm
          subst hmm
          refine .vis rfl (path_div_of cs (k n) (k' n)
            (fun c hc => hl c (List.mem_cons_of_mem _ hc)) (fun cs' hl' => ?_) hp')
          have hl'' : ∀ c ∈ (⟨m, n⟩ :: cs' : List (Call E)), P c := by
            intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact hl _ (List.mem_cons.2 (.inl rfl))
            · exact hl' c hc
          obtain ⟨h₁, h₂⟩ := h _ hl''
          have e₁ : ∀ a, Path (vis (⟨m, rfl⟩ : SigEv E (E.Ar m)) k) (⟨m, n⟩ :: cs') (.val a) ↔
              Path (k n) cs' (.val a) := fun _ =>
            path_vis_cons (e := (⟨m, rfl⟩ : SigEv E (E.Ar m))) (r := n)
          have e₂ : ∀ a, Path (vis (⟨m, rfl⟩ : SigEv E (E.Ar m)) k') (⟨m, n⟩ :: cs') (.val a) ↔
              Path (k' n) cs' (.val a) := fun _ =>
            path_vis_cons (e := (⟨m, rfl⟩ : SigEv E (E.Ar m))) (r := n)
          have q₁ : ∀ m₁, Pend (vis (⟨m, rfl⟩ : SigEv E (E.Ar m)) k) (⟨m, n⟩ :: cs') m₁ ↔
              Pend (k n) cs' m₁ := fun _ =>
            pend_vis_cons (e := (⟨m, rfl⟩ : SigEv E (E.Ar m))) (r := n)
          have q₂ : ∀ m₁, Pend (vis (⟨m, rfl⟩ : SigEv E (E.Ar m)) k') (⟨m, n⟩ :: cs') m₁ ↔
              Pend (k' n) cs' m₁ := fun _ =>
            pend_vis_cons (e := (⟨m, rfl⟩ : SigEv E (E.Ar m))) (r := n)
          exact ⟨(exists_congr e₁).symm.trans (h₁.trans (exists_congr e₂)),
            fun m₁ => (q₁ m₁).symm.trans ((h₂ m₁).trans (q₂ m₁))⟩
        · cases hc

end

/-! ## Legal calls -/

section
variable {E : Sig.{u}} {S T A B : Type (u + 1)}
  (L : (m : (liftSig E).Op) → (liftSig E).Ar m → Prop)

/-- A call of `E` whose lifted answer is legal. -/
def LegalC (c : Call E) : Prop := L (ULift.up c.1) (ULift.up c.2)

/-- A legally answered call, lowered to `E`. -/
def lowerL (x : Call (legalSig (liftSig E) L)) : Call E := ⟨x.1.down, x.2.1.down⟩

theorem legalC_lowerL (x : Call (legalSig (liftSig E) L)) : LegalC L (lowerL L x) := x.2.2

theorem map_liftCall_lowerL (l : List (Call (legalSig (liftSig E) L))) :
    (l.map (lowerL L)).map liftCallB = l.map liftCallL := by
  rw [List.map_map]; rfl

theorem legal_map_lowerL (l : List (Call (legalSig (liftSig E) L))) :
    ∀ c ∈ l.map (lowerL L), LegalC L c := by
  intro c hc
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
  exact legalC_lowerL L x

theorem exists_lowerL :
    ∀ (cs : List (Call E)), (∀ c ∈ cs, LegalC L c) →
      ∃ l : List (Call (legalSig (liftSig E) L)), l.map (lowerL L) = cs
  | [], _ => ⟨[], rfl⟩
  | c :: cs, h => by
    obtain ⟨l, hl⟩ := exists_lowerL cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    exact ⟨⟨ULift.up c.1, ⟨ULift.up c.2, h c (List.mem_cons.2 (.inl rfl))⟩⟩ :: l,
      by rw [List.map_cons, hl]; rfl⟩

theorem map_liftCall_inj : ∀ {cs cs' : List (Call E)},
    cs.map liftCallB = cs'.map liftCallB → cs = cs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, c' :: cs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : c = c' := congrArg (fun x : Call (liftSig E) => (⟨x.1.down, x.2.down⟩ : Call E)) h1
    rw [this, map_liftCall_inj h2]

theorem mem_toAFun_iff (f : Hom E S T A B) (s : S) (a : A) (cs : List (Call E)) (e : End S B) :
    (cs.map liftCallB, e) ∈ toAFun f s a ↔
      ∃ r, Path ((f a).run s).run cs r ∧ e = endOf r := by
  constructor
  · rintro ⟨cs', r, hp, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    obtain rfl := map_liftCall_inj h1
    exact ⟨r, hp, rfl⟩
  · rintro ⟨r, hp, rfl⟩
    exact ⟨cs, r, hp, rfl⟩

theorem mem_toPending_iff (f : Hom E S T A B) (s : S) (a : A) (cs : List (Call E))
    (m : (liftSig E).Op) :
    (cs.map liftCallB, m) ∈ toPending f s a ↔ Pend ((f a).run s).run cs m.down := by
  constructor
  · rintro ⟨cs', m', hp, he⟩
    injection he with h1 h2
    subst h2
    obtain rfl := map_liftCall_inj h1
    exact hp
  · intro hp
    exact ⟨cs, m.down, hp, rfl⟩

theorem take_map' {α : Type v} {β : Type w} (g : α → β) (ω : Stream' α) (n : Nat) :
    (Stream'.map g ω).take n = (ω.take n).map g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Stream'.take_succ', Stream'.take_succ', ih, List.map_append]; rfl

/-- **Legal infinite streams are the limits of legal pending prefixes.** -/
theorem mem_restrict_inf_iff (f : Hom E S T A B) (s : S) (a : A)
    (ω : Nat → Call (legalSig (liftSig E) L)) :
    ω ∈ (restrict L (toTriple f)).2.2 s a ↔
      ∀ n, ∃ m, (Stream'.take n ω, m) ∈ (restrict L (toTriple f)).2.1 s a := by
  change (fun k => liftCallL (ω k)) ∈ toInf f s a ↔
    ∀ n, ∃ m, ((Stream'.take n ω).map liftCallL, m) ∈ toPending f s a
  refine (mem_toInf_iff f s a (fun k => liftCallL (ω k))).trans
    (forall_congr' fun n => exists_congr fun m => Iff.of_eq ?_)
  exact congrArg (fun l => (l, m) ∈ toPending f s a) (take_map' liftCallL ω n)

theorem endOf_ret_inv {b : B} {s' : S} {r : PathEnd (Except T (B × S))}
    (h : End.ret b s' = endOf r) : r = .val (.ok (b, s')) := by
  rcases r with (e | ⟨b', s''⟩) | _
  · cases h
  · cases h; rfl
  · cases h

theorem endOf_trap_inv {r : PathEnd (Except T (B × S))} (h : (End.trap : End S B) = endOf r) :
    ∃ e, r = .val (.error e) := by
  rcases r with (e | ⟨b', s''⟩) | _
  · exact ⟨e, rfl⟩
  · cases h
  · cases h

theorem endOf_div_inv {r : PathEnd (Except T (B × S))} (h : (End.div : End S B) = endOf r) :
    r = .div := by
  rcases r with (e | ⟨b', s''⟩) | _
  · cases h
  · cases h
  · rfl

/-- **Agreement at legal logs**: the same non-trap finished paths, the same traps up to their
payload, and the same pending calls, at every legal log. -/
def LObs (f g : Hom E S T A B) : Prop :=
  ∀ (s : S) (a : A) (cs : List (Call E)), (∀ c ∈ cs, LegalC L c) →
    (∀ (b : B) (s' : S), Path ((f a).run s).run cs (.val (.ok (b, s'))) ↔
      Path ((g a).run s).run cs (.val (.ok (b, s')))) ∧
    ((∃ e, Path ((f a).run s).run cs (.val (.error e))) ↔
      ∃ e, Path ((g a).run s).run cs (.val (.error e))) ∧
    ∀ m, Pend ((f a).run s).run cs m ↔ Pend ((g a).run s).run cs m

theorem lObs_val {f g : Hom E S T A B} (h : LObs L f g) (s : S) (a : A) :
    ∀ cs', (∀ c ∈ cs', LegalC L c) →
      ((∃ v, Path ((f a).run s).run cs' (.val v)) ↔ ∃ v, Path ((g a).run s).run cs' (.val v)) ∧
        ∀ m, Pend ((f a).run s).run cs' m ↔ Pend ((g a).run s).run cs' m := by
  intro cs' hl
  obtain ⟨h₁, h₂, h₃⟩ := h s a cs' hl
  refine ⟨⟨fun ⟨v, hv⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩, h₃⟩
  · rcases v with e | ⟨b, s'⟩
    · obtain ⟨e', he'⟩ := h₂.1 ⟨e, hv⟩; exact ⟨_, he'⟩
    · exact ⟨_, (h₁ b s').1 hv⟩
  · rcases v with e | ⟨b, s'⟩
    · obtain ⟨e', he'⟩ := h₂.2 ⟨e, hv⟩; exact ⟨_, he'⟩
    · exact ⟨_, (h₁ b s').2 hv⟩

/-- **The restricted triple is exactly the agreement at legal logs.** -/
theorem restrict_eq_iff (f g : Hom E S T A B) :
    restrict L (toTriple f) = restrict L (toTriple g) ↔ LObs L f g := by
  constructor
  · intro h s a cs hcs
    obtain ⟨l, rfl⟩ := exists_lowerL L cs hcs
    have h1 : ∀ e, ((l.map (lowerL L)).map liftCallB, e) ∈ toAFun f s a ↔
        ((l.map (lowerL L)).map liftCallB, e) ∈ toAFun g s a := fun e => by
      rw [map_liftCall_lowerL]
      exact Set.ext_iff.1 (congrFun (congrFun (congrArg (·.1) h) s) a) (l, e)
    have h2 : ∀ m, ((l.map (lowerL L)).map liftCallB, m) ∈ toPending f s a ↔
        ((l.map (lowerL L)).map liftCallB, m) ∈ toPending g s a := fun m => by
      rw [map_liftCall_lowerL]
      exact Set.ext_iff.1 (congrFun (congrFun (congrArg (·.2.1) h) s) a) (l, m)
    refine ⟨fun b s' => ?_, ?_, fun m => ?_⟩
    · have := h1 (.ret b s')
      rw [mem_toAFun_iff, mem_toAFun_iff] at this
      exact ⟨fun hp => by obtain ⟨r, hr, he⟩ := this.1 ⟨_, hp, rfl⟩; rwa [endOf_ret_inv he] at hr,
        fun hp => by obtain ⟨r, hr, he⟩ := this.2 ⟨_, hp, rfl⟩; rwa [endOf_ret_inv he] at hr⟩
    · have := h1 .trap
      rw [mem_toAFun_iff, mem_toAFun_iff] at this
      refine ⟨fun ⟨e, hp⟩ => ?_, fun ⟨e, hp⟩ => ?_⟩
      · obtain ⟨r, hr, he⟩ := this.1 ⟨_, hp, rfl⟩
        obtain ⟨e', rfl⟩ := endOf_trap_inv he
        exact ⟨e', hr⟩
      · obtain ⟨r, hr, he⟩ := this.2 ⟨_, hp, rfl⟩
        obtain ⟨e', rfl⟩ := endOf_trap_inv he
        exact ⟨e', hr⟩
    · exact (mem_toPending_iff f s a _ (ULift.up m)).symm.trans
        ((h2 (ULift.up m)).trans (mem_toPending_iff g s a _ (ULift.up m)))
  · intro h
    have hP : (restrict L (toTriple f)).2.1 = (restrict L (toTriple g)).2.1 := by
      funext s a
      ext ⟨l, m⟩
      change (l.map liftCallL, m) ∈ toPending f s a ↔
        (l.map liftCallL, m) ∈ toPending g s a
      rw [← map_liftCall_lowerL]
      exact (mem_toPending_iff f s a _ m).trans
        (((h s a _ (legal_map_lowerL L l)).2.2 m.down).trans (mem_toPending_iff g s a _ m).symm)
    have hA : (restrict L (toTriple f)).1 = (restrict L (toTriple g)).1 := by
      funext s a
      ext ⟨l, e⟩
      change (l.map liftCallL, e) ∈ toAFun f s a ↔
        (l.map liftCallL, e) ∈ toAFun g s a
      rw [← map_liftCall_lowerL, mem_toAFun_iff, mem_toAFun_iff]
      have hl := legal_map_lowerL L l
      obtain ⟨h₁, h₂, -⟩ := h s a _ hl
      cases e with
      | ret b s' =>
        constructor
        · rintro ⟨r, hr, he⟩
          rw [endOf_ret_inv he] at hr
          exact ⟨_, (h₁ b s').1 hr, rfl⟩
        · rintro ⟨r, hr, he⟩
          rw [endOf_ret_inv he] at hr
          exact ⟨_, (h₁ b s').2 hr, rfl⟩
      | trap =>
        constructor
        · rintro ⟨r, hr, he⟩
          obtain ⟨e', rfl⟩ := endOf_trap_inv he
          obtain ⟨e'', he''⟩ := h₂.1 ⟨e', hr⟩
          exact ⟨_, he'', rfl⟩
        · rintro ⟨r, hr, he⟩
          obtain ⟨e', rfl⟩ := endOf_trap_inv he
          obtain ⟨e'', he''⟩ := h₂.2 ⟨e', hr⟩
          exact ⟨_, he'', rfl⟩
      | div =>
        have hv := lObs_val L h s a
        constructor
        · rintro ⟨r, hr, he⟩
          rw [endOf_div_inv he] at hr
          exact ⟨_, path_div_of _ _ _ hl hv hr, rfl⟩
        · rintro ⟨r, hr, he⟩
          rw [endOf_div_inv he] at hr
          refine ⟨_, path_div_of _ _ _ hl (fun cs' hl' => ?_) hr, rfl⟩
          obtain ⟨hv₁, hv₂⟩ := hv cs' hl'
          exact ⟨hv₁.symm, fun m => (hv₂ m).symm⟩
    have hI : (restrict L (toTriple f)).2.2 = (restrict L (toTriple g)).2.2 := by
      funext s a
      ext ω
      rw [mem_restrict_inf_iff, mem_restrict_inf_iff, hP]
    exact Prod.ext hA (Prod.ext hP hI)

end

end Silmaril.Proofs.Wasm.Abstract.LegalStrat

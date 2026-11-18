module

public import Silmaril.Proofs.Wasm.Component.InstSem.Algebra
public import Silmaril.Games.Reduct.Thms

/-!
# The component IR with an instantiation phase: plays after instantiation

* `mem_comp_pure_iff`: a question that a handler on top answers at once (`h q = pure a`)
  leaves the composite where it was.
* `mem_withReady_iff`: `[inst, ready] ++ p` (lifted) is a play of `withReady τ` iff `p` is a play
  of `τ`.
* `mem_instGuard_iff`: a play following the instantiation protocol is a play of `instGuard σ`
  iff it is a play of `σ`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component
open Silmaril.Wasm.Game (liftMove liftEv)

variable {E F G : Sig.{0}} {R : Type}

/-! ## Runs of handlers -/

section Handler

variable {h : Handler F G}

/-- A handler makes no silent step: a run's first move is a step. -/
theorem handler_run_cons {x z : h.toReduction.toLTS.State} {o : Move F G} {s : List (Move F G)}
    (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, Reduction.Step h.toReduction x (some o) y ∧ h.toReduction.toLTS.Run y s z := by
  cases hr with
  | tau hs _ => cases hs with | tau hc => exact (hc : False).elim
  | vis hs hr => exact ⟨_, hs, hr⟩

/-- From `idle`, a handler first accepts a question. -/
theorem handler_run_idle_cons {o : Move F G} {t : List (Move F G)}
    {y : h.toReduction.toLTS.State} (hr : h.toReduction.toLTS.Run .idle (o :: t) y) :
    ∃ q, o = .inr (.ask q) ∧ h.toReduction.toLTS.Run (.run q (h q)) t y := by
  obtain ⟨x', hs, hr⟩ := handler_run_cons hr
  cases hs with
  | ask q => exact ⟨q, rfl, hr⟩

/-- A handler whose program is `pure a` answers `a` and is idle again. -/
theorem handler_run_pure_cons {q : G.Op} {a : G.Ar q} {o : Move F G} {t : List (Move F G)}
    {y : h.toReduction.toLTS.State}
    (hr : h.toReduction.toLTS.Run (.run q (.pure a)) (o :: t) y) :
    o = .inr (.ans q a) ∧ h.toReduction.toLTS.Run .idle t y := by
  obtain ⟨x', hs, hr'⟩ := handler_run_cons hr
  cases hs with
  | call hc => cases hc
  | ret hd => cases hd; exact ⟨rfl, hr'⟩

end Handler

/-- **A question answered at once by the handler on top leaves the composite where it was.** -/
theorem mem_comp_pure_iff {σ : Strategy E F} {h : Handler F G} {q : G.Op} {a : G.Ar q}
    (hq : h q = .pure a) (x : List (Move E G)) :
    .inr (.ask q) :: .inr (.ans q a) :: x ∈ σ.comp (Strategy.ofHandler h) ↔
      x ∈ σ.comp (Strategy.ofHandler h) := by
  constructor
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 ht
    cases hz with
    | sync b hz =>
      obtain ⟨_, he, -⟩ := handler_run_idle_cons hy
      cases he
    | right c hz =>
      obtain ⟨q', he, hy⟩ := handler_run_idle_cons hy
      cases he
      rw [hq] at hy
      cases hz with
      | sync b hz =>
        obtain ⟨he, -⟩ := handler_run_pure_cons hy
        cases he
      | right c hz =>
        obtain ⟨he, hy⟩ := handler_run_pure_cons hy
        cases he
        exact ⟨s, hs, _, Strategy.mem_ofHandler.2 ⟨y, hy⟩, hz⟩
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 ht
    refine ⟨s, hs, _, Strategy.mem_ofHandler.2 ⟨y, ?_⟩, .right _ (.right _ hz)⟩
    refine .vis (.ask q) (.vis (.ret ?_) hy)
    show h q = .pure a
    exact hq

/-! ## Lifted plays -/

/-- A position of `E ↠ F` as a position of `E ↠ F.withInst R`. -/
def liftPos : Pos E F → Pos E (F.withInst R)
  | .idle => .idle
  | .run q => .run (some q)
  | .wait q m => .wait (some q) m

theorem path_of_lift : ∀ {p : List (Move E F)} {x : Pos E F} {z : Pos E (F.withInst R)},
    Path (liftPos x) (p.map liftMove) z → ∃ z', Path x p z'
  | [], x, _, _ => ⟨x, .nil _⟩
  | o :: p, x, z, .cons hs hp => by
    rcases o with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩) <;> cases x <;> cases hs
    · obtain ⟨z', h⟩ := path_of_lift (x := .wait _ m) hp
      exact ⟨z', .cons (.call _ m) h⟩
    · obtain ⟨z', h⟩ := path_of_lift (x := .run _) hp
      exact ⟨z', .cons (.reply _ m n) h⟩
    · obtain ⟨z', h⟩ := path_of_lift (x := .run q) hp
      exact ⟨z', .cons (.ask q) h⟩
    · obtain ⟨z', h⟩ := path_of_lift (x := .idle) hp
      exact ⟨z', .cons (.ret q n) h⟩

/-- The lift of a legal play is legal only if the play is. -/
theorem legal_of_lift {p : List (Move E F)} (h : Legal (p.map (liftMove (R := R)))) : Legal p := by
  obtain ⟨z, hz⟩ := h
  exact path_of_lift (x := .idle) hz

/-- The plays seen through the export renaming are the lifted ones. -/
theorem forall₂_upRel_iff {s : List (Move E (F.withInst R))} {p : List (Move E F)} :
    List.Forall₂ (UpRel (exHom F R)) s p ↔ s = p.map liftMove := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hab _ ih =>
      subst ih
      cases hab <;> rfl
  · rintro rfl
    induction p with
    | nil => exact .nil
    | cons o p ih =>
      refine .cons ?_ ih
      rcases o with e | (⟨q⟩ | ⟨q, n⟩)
      · exact .low e
      · exact .ask (ρ := exHom F R) q
      · exact .ans (ρ := exHom F R) q n

/-- **After a ready-at-once instantiation, `withReady τ` plays `τ`.** -/
theorem mem_withReady_iff (τ : Strategy E F) (p : List (Move E F)) :
    askInst :: ansInst .ready :: p.map liftMove ∈ withReady (R := R) τ ↔ p ∈ τ := by
  have hres : (withReady (R := R) τ).restrict (exHom F R) = τ := by
    rw [Strategy.restrict, withReady, Strategy.comp_assoc, ← Strategy.ofHandler_comp,
      readyH_comp_exH, Strategy.ofHandler_id, Strategy.comp_id]
  refine (mem_comp_pure_iff (σ := τ) (h := readyH F R) (q := none) (a := InstAns.ready) rfl
    _).trans ?_
  constructor
  · intro h
    rw [← hres]
    exact Strategy.restrict_complete _ _ h (forall₂_upRel_iff.2 rfl)
      (legal_of_lift ((withReady τ).legal h))
  · intro h
    rw [← hres] at h
    obtain ⟨s, hs, hr⟩ := Strategy.restrict_sound' _ _ h
    rwa [forall₂_upRel_iff.1 hr] at hs

/-! ## The protocol guard -/

theorem instGuard_le (σ : Strategy E (F.withInst R)) : instGuard σ ≤ σ :=
  Strategy.generate_le fun _ hs _ => hs.1

/-- **On plays following the protocol, the guard changes nothing.** -/
theorem mem_instGuard_iff {σ : Strategy E (F.withInst R)} {p : List (Move E (F.withInst R))}
    (hp : InstProper p) : p ∈ instGuard σ ↔ p ∈ σ :=
  ⟨fun h => instGuard_le σ h, fun h => Strategy.subset_generate ⟨h, hp⟩ (σ.legal h)⟩

theorem upper_map_liftMove : ∀ p : List (Move E F),
    upper (p.map (liftMove (R := R))) = (upper p).map liftEv
  | [] => rfl
  | .inl _ :: p => by simp only [List.map_cons, liftMove, Sum.map_inl, upper,
      List.filterMap_cons, Sum.getRight?_inl]; exact upper_map_liftMove p
  | .inr _ :: p => by simp only [List.map_cons, liftMove, Sum.map_inr, upper,
      List.filterMap_cons, Sum.getRight?_inr, List.map_cons]; exact congrArg _ (upper_map_liftMove p)

theorem instProper_ready (p : List (Move E F)) :
    InstProper (askInst :: ansInst (R := R) .ready :: p.map liftMove) := by
  refine .inr (.inr (.inr ⟨(upper p).map liftEv, ?_, ?_⟩))
  · simp only [upper, askInst, ansInst, List.filterMap_cons, Sum.getRight?_inr]
    exact congrArg _ (congrArg _ (upper_map_liftMove p))
  · intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    cases y <;> rfl

/-- **The guard does not change the plays after a ready-at-once instantiation.** -/
theorem afterReady_instGuard (σ : Strategy E (F.withInst R)) (p : List (Move E F)) :
    askInst :: ansInst .ready :: p.map liftMove ∈ instGuard σ ↔
      askInst :: ansInst .ready :: p.map liftMove ∈ σ :=
  mem_instGuard_iff (instProper_ready p)

variable {M : Type} [CoreModule M]

/-- **For start-free core semantics, the plays of the instantiating denotation after
instantiation are the plays of the start-free denotation.** -/
theorem denI_toI_iff (C : CoreSem M) (c : Comp M) (p : List (Move sigU sigU)) :
    askInst :: ansInst .ready :: p.map liftMove ∈ c.denI C.toI ↔ p ∈ c.denU C := by
  rw [Comp.denI, afterReady_instGuard, denIR_toI, mem_withReady_iff]

end Silmaril.Proofs.Wasm.Component.InstSem

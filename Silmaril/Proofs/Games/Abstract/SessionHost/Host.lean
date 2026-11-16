module

public import Silmaril.Games.Abstract.SessionHost.Defs
public import Silmaril.Games.Composition.Defs

/-!
# The host beside copycat as an automaton (proofs)

`hostCopy F R : DStrategy F (E ⊕ₛ F)` answers the host calls `E` per `R` and forwards the
component calls `F` to the lower interface, one call at a time (`HSt`, `HStep`, `HRun`). It is the
pairing `(hostDOn F R).pair (DStrategy.id F)` (`SessionHost.Pair`).

An interaction of `hostCopy` with an upper play `v` of `E ⊕ₛ F ↠ G`:

* `zip_hmv`: `hmv v`, the host moves answering `v`, interacts with `v` leaving `vis v` visible:
  the host calls hidden, the component calls renamed to the lower interface;
* `hrun_hmv`: `hmv v` is a run of the automaton when the host answers of `v` are allowed;
* `zip_fwd`: conversely every interaction has this visible part, up to the one forwarded move in
  flight (`aOf`, `bOf`), and every host answer of `v` is allowed.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost

universe u

variable {E F G : Sig.{u}} {R : HostRel E}

/-! ## The automaton -/

/-- States of the host beside copycat: idle, answering a host call, forwarding a component call
(asked, waiting for the lower answer, answered). -/
inductive HSt (E F : Sig.{u}) : Type u
  | idle
  | waitE (m : E.Op)
  | askF (m : F.Op)
  | waitF (m : F.Op)
  | ansF (m : F.Op) (n : F.Ar m)

/-- The game position of a state. -/
def HSt.pos : HSt E F → Pos F (E ⊕ₛ F)
  | .idle => .idle
  | .waitE m => .run (.inl m)
  | .askF m => .run (.inr m)
  | .waitF m => .wait (.inr m) m
  | .ansF m _ => .run (.inr m)

/-- One move of the host beside copycat. -/
inductive HStep (R : HostRel E) : HSt E F → Move F (E ⊕ₛ F) → HSt E F → Prop
  | askE (m : E.Op) : HStep R .idle (.inr (.ask (.inl m))) (.waitE m)
  | ansE (m : E.Op) (n : E.Ar m) : R m (.answer n) →
      HStep R (.waitE m) (.inr (.ans (.inl m) n)) .idle
  | askF (m : F.Op) : HStep R .idle (.inr (.ask (.inr m))) (.askF m)
  | fwdF (m : F.Op) : HStep R (.askF m) (.inl (.ask m)) (.waitF m)
  | replyF (m : F.Op) (n : F.Ar m) : HStep R (.waitF m) (.inl (.ans m n)) (.ansF m n)
  | retF (m : F.Op) (n : F.Ar m) : HStep R (.ansF m n) (.inr (.ans (.inr m) n)) .idle

/-- Runs of the host beside copycat. -/
inductive HRun (R : HostRel E) : HSt E F → List (Move F (E ⊕ₛ F)) → HSt E F → Prop
  | nil (x : HSt E F) : HRun R x [] x
  | cons {x y z : HSt E F} {o : Move F (E ⊕ₛ F)} {s : List (Move F (E ⊕ₛ F))} :
      HStep R x o y → HRun R y s z → HRun R x (o :: s) z

theorem HStep.pos {x y : HSt E F} {o : Move F (E ⊕ₛ F)} (h : HStep R x o y) :
    Step x.pos o y.pos := by
  cases h <;> constructor

theorem HRun.pos {x y : HSt E F} {s : List (Move F (E ⊕ₛ F))} (h : HRun R x s y) :
    Path x.pos s y.pos := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons h.pos ih

theorem HRun.append {x y z : HSt E F} {s t : List (Move F (E ⊕ₛ F))} (h₁ : HRun R x s y)
    (h₂ : HRun R y t z) : HRun R x (s ++ t) z := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem HRun.of_append {x z : HSt E F} {s t : List (Move F (E ⊕ₛ F))}
    (h : HRun R x (s ++ t) z) : ∃ y, HRun R x s y ∧ HRun R y t z := by
  induction s generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o s ih =>
    cases h with
    | cons h hr => obtain ⟨y, h₁, h₂⟩ := ih hr; exact ⟨y, .cons h h₁, h₂⟩

theorem HRun.single {x y : HSt E F} {o : Move F (E ⊕ₛ F)} (h : HStep R x o y) :
    HRun R x [o] y := .cons h (.nil _)

theorem HStep.det {x y y' : HSt E F} {o : Move F (E ⊕ₛ F)} (h : HStep R x o y)
    (h' : HStep R x o y') : y = y' := by
  cases h <;> cases h' <;> rfl

theorem HRun.det {x y y' : HSt E F} {s : List (Move F (E ⊕ₛ F))} (h : HRun R x s y)
    (h' : HRun R x s y') : y = y' := by
  induction h with
  | nil => cases h'; rfl
  | cons hs _ ih =>
    cases h' with
    | cons hs' hr' => cases hs.det hs'; exact ih hr'

/-- Every legal Opponent move is accepted. -/
theorem HRun.receptive {h : HSt E F} {s : List (Move F (E ⊕ₛ F))} {x y : Pos F (E ⊕ₛ F)}
    {o : Move F (E ⊕ₛ F)} (hr : HRun R .idle s h) (hx : Path .idle s x) (hs : Step x o y)
    (ho : o.IsO) : ∃ h', HRun R .idle (s ++ [o]) h' := by
  cases hr.pos.det hx
  cases h with
  | idle =>
    cases hs with
    | ask q =>
      rcases q with m | m
      · exact ⟨_, hr.append (.single (.askE m))⟩
      · exact ⟨_, hr.append (.single (.askF m))⟩
  | waitE m => cases hs <;> exact ho.elim
  | askF m => cases hs <;> exact ho.elim
  | waitF m =>
    cases hs with
    | reply q m n => exact ⟨_, hr.append (.single (.replyF m n))⟩
  | ansF m n => cases hs <;> exact ho.elim

/-- The finite plays of the host beside copycat. -/
def hostCopyS (F : Sig.{u}) (R : HostRel E) : Strategy F (E ⊕ₛ F) where
  plays := {p | ∃ h, HRun R .idle p h}
  nil_mem := ⟨_, .nil _⟩
  legal := fun ⟨_, h⟩ => ⟨_, h.pos⟩
  of_prefix := by
    rintro s _ ⟨h, hr⟩ ⟨u, rfl⟩
    obtain ⟨z, hz, -⟩ := hr.of_append
    exact ⟨z, hz⟩
  receptive := fun ⟨_, hr⟩ hx hs ho => hr.receptive hx hs ho

/-- **The host beside copycat**: host calls answered per `R`, diverging where `R` may diverge;
component calls forwarded; every limit of plays an infinite play. -/
def hostCopy (F : Sig.{u}) (R : HostRel E) : DStrategy F (E ⊕ₛ F) where
  toStrategy := hostCopyS F R
  div := {p | ∃ m, HRun R .idle p (.waitE m) ∧ R m .diverge}
  inf := {I | IsInfPlay I ∧ I ⊆ (hostCopyS F R).plays}
  div_mem := fun ⟨_, h, _⟩ => ⟨_, h⟩
  div_run := fun ⟨m, h, _⟩ => ⟨.inl m, h.pos⟩
  inf_isInf h := h.1
  inf_sub h := h.2

/-! ## Visible parts and host moves -/

/-- The visible part of an upper move: host calls hidden, component calls on the lower
interface. -/
def visMove : Move (E ⊕ₛ F) G → List (Move F G)
  | .inr c => [.inr c]
  | .inl (.ask (.inl _)) => []
  | .inl (.ans (.inl _) _) => []
  | .inl (.ask (.inr m)) => [.inl (.ask m)]
  | .inl (.ans (.inr m) n) => [.inl (.ans m n)]

/-- The visible part of an upper play. -/
def vis : List (Move (E ⊕ₛ F) G) → List (Move F G)
  | [] => []
  | o :: v => visMove o ++ vis v

/-- The host moves answering an upper move. -/
def hmvMove : Move (E ⊕ₛ F) G → List (Move F (E ⊕ₛ F))
  | .inr _ => []
  | .inl (.ask (.inl m)) => [.inr (.ask (.inl m))]
  | .inl (.ans (.inl m) n) => [.inr (.ans (.inl m) n)]
  | .inl (.ask (.inr m)) => [.inr (.ask (.inr m)), .inl (.ask m)]
  | .inl (.ans (.inr m) n) => [.inl (.ans m n), .inr (.ans (.inr m) n)]

/-- The host moves answering an upper play. -/
def hmv : List (Move (E ⊕ₛ F) G) → List (Move F (E ⊕ₛ F))
  | [] => []
  | o :: v => hmvMove o ++ hmv v

@[simp] theorem vis_nil : vis ([] : List (Move (E ⊕ₛ F) G)) = [] := rfl

@[simp] theorem vis_cons (o : Move (E ⊕ₛ F) G) (v : List (Move (E ⊕ₛ F) G)) :
    vis (o :: v) = visMove o ++ vis v := rfl

@[simp] theorem vis_append (v w : List (Move (E ⊕ₛ F) G)) : vis (v ++ w) = vis v ++ vis w := by
  induction v with
  | nil => rfl
  | cons o v ih => simp [ih]

@[simp] theorem hmv_append (v w : List (Move (E ⊕ₛ F) G)) : hmv (v ++ w) = hmv v ++ hmv w := by
  induction v with
  | nil => rfl
  | cons o v ih => simp [hmv, ih]

theorem vis_prefix {v w : List (Move (E ⊕ₛ F) G)} (h : v <+: w) : vis v <+: vis w := by
  obtain ⟨u, rfl⟩ := h; rw [vis_append]; exact List.prefix_append _ _

theorem hmv_prefix {v w : List (Move (E ⊕ₛ F) G)} (h : v <+: w) : hmv v <+: hmv w := by
  obtain ⟨u, rfl⟩ := h; rw [hmv_append]; exact List.prefix_append _ _

theorem length_visMove_le (o : Move (E ⊕ₛ F) G) : (visMove o).length ≤ 1 := by
  rcases o with ((m | m) | ⟨(m | m), n⟩) | c <;> simp [visMove]

theorem length_vis_le (v : List (Move (E ⊕ₛ F) G)) : (vis v).length ≤ v.length := by
  induction v with
  | nil => exact le_rfl
  | cons o v ih => have := length_visMove_le o; simp; omega

/-- `hmv v` interacts with `v`, leaving `vis v` visible. -/
theorem zip_hmv (v : List (Move (E ⊕ₛ F) G)) : Zip (hmv v) v (vis v) := by
  induction v with
  | nil => exact .nil
  | cons o v ih =>
    rcases o with ((m | m) | ⟨(m | m), n⟩) | c
    · exact .sync _ ih
    · exact .sync _ (.left _ ih)
    · exact .sync _ ih
    · exact .left _ (.sync _ ih)
    · exact .right _ ih

/-- A host answer of an upper move is allowed. -/
def OkMove (R : HostRel E) : Move (E ⊕ₛ F) G → Prop
  | .inl (.ans (.inl m) n) => R m (.answer n)
  | _ => True

/-- Every host answer of an upper play is allowed. -/
def OkV (R : HostRel E) (v : List (Move (E ⊕ₛ F) G)) : Prop := ∀ o ∈ v, OkMove R o

theorem OkV.nil : OkV R ([] : List (Move (E ⊕ₛ F) G)) := fun _ h => nomatch h

theorem okV_cons {o : Move (E ⊕ₛ F) G} {v : List (Move (E ⊕ₛ F) G)} :
    OkV R (o :: v) ↔ OkMove R o ∧ OkV R v := List.forall_mem_cons

theorem okV_append {v w : List (Move (E ⊕ₛ F) G)} : OkV R (v ++ w) ↔ OkV R v ∧ OkV R w :=
  List.forall_mem_append

theorem OkV.of_prefix {v w : List (Move (E ⊕ₛ F) G)} (h : OkV R w) (hv : v <+: w) : OkV R v :=
  fun o ho => h o (hv.subset ho)

/-- The host state answering an upper position. -/
def hOf : Pos (E ⊕ₛ F) G → HSt E F
  | .idle => .idle
  | .run _ => .idle
  | .wait _ (.inl m) => .waitE m
  | .wait _ (.inr m) => .waitF m

/-- **The host moves answering an upper play are a run** when its host answers are allowed. -/
theorem hrun_hmv {x y : Pos (E ⊕ₛ F) G} {v : List (Move (E ⊕ₛ F) G)} (h : Path x v y)
    (hv : OkV R v) : HRun R (hOf x) (hmv v) (hOf y) := by
  induction h with
  | nil => exact .nil _
  | cons st _ ih =>
    obtain ⟨ho, hv⟩ := okV_cons.1 hv
    have ih := ih hv
    cases st with
    | ask q => exact ih
    | call q μ =>
      rcases μ with m | m
      · exact .cons (.askE m) ih
      · exact .cons (.askF m) (.cons (.fwdF m) ih)
    | reply q μ n =>
      rcases μ with m | m
      · exact .cons (.ansE m n ho) ih
      · exact .cons (.replyF m n) (.cons (.retF m n) ih)
    | ret q r => exact ih

/-! ## The visible part of an interaction -/

/-- The host state agrees with the position of the upper play. -/
inductive Compat : HSt E F → Pos (E ⊕ₛ F) G → Prop
  | idle : Compat .idle .idle
  | run (g : G.Op) : Compat .idle (.run g)
  | waitE (g : G.Op) (m : E.Op) : Compat (.waitE m) (.wait g (.inl m))
  | askF (g : G.Op) (m : F.Op) : Compat (.askF m) (.wait g (.inr m))
  | waitF (g : G.Op) (m : F.Op) : Compat (.waitF m) (.wait g (.inr m))
  | ansF (g : G.Op) (m : F.Op) (n : F.Ar m) : Compat (.ansF m n) (.wait g (.inr m))

/-- The forwarded call not yet visible. -/
def aOf : HSt E F → List (Move F G)
  | .askF m => [.inl (.ask m)]
  | _ => []

/-- The forwarded answer not yet hidden. -/
def bOf : HSt E F → List (Move F G)
  | .ansF m n => [.inl (.ans m n)]
  | _ => []

theorem length_aOf_le (h : HSt E F) : (aOf h : List (Move F G)).length ≤ 1 := by
  cases h <;> simp [aOf]

theorem length_bOf_le (h : HSt E F) : (bOf h : List (Move F G)).length ≤ 1 := by
  cases h <;> simp [bOf]

/-- **Forward**: in an interaction of the host beside copycat with an upper play, every host
answer is allowed, and the visible part is the visible part of the upper play up to the move in
flight. -/
theorem zip_fwd {sH : List (Move F (E ⊕ₛ F))} {v : List (Move (E ⊕ₛ F) G)}
    {q : List (Move F G)} (hz : Zip sH v q) :
    ∀ {h₀ h₁ : HSt E F} {x y : Pos (E ⊕ₛ F) G}, HRun R h₀ sH h₁ → Path x v y → Compat h₀ x →
      Compat h₁ y ∧ OkV R v ∧ bOf h₀ ++ q ++ aOf h₁ = aOf h₀ ++ vis v ++ bOf h₁ := by
  induction hz with
  | nil =>
    intro h₀ h₁ x y hr hp hc
    cases hr; cases hp
    refine ⟨hc, OkV.nil, ?_⟩
    cases h₀ <;> simp [aOf, bOf]
  | left a _ ih =>
    intro h₀ h₁ x y hr hp hc
    cases hr with
    | cons hs hr =>
      cases hs with
      | fwdF m =>
        cases hc with
        | askF g m =>
          obtain ⟨hc', hok, he⟩ := ih hr hp (.waitF g m)
          refine ⟨hc', hok, ?_⟩
          simp [aOf, bOf] at he ⊢; exact he
      | replyF m n =>
        cases hc with
        | waitF g m =>
          obtain ⟨hc', hok, he⟩ := ih hr hp (.ansF g m n)
          refine ⟨hc', hok, ?_⟩
          simp [aOf, bOf] at he ⊢; exact he
  | right c _ ih =>
    intro h₀ h₁ x y hr hp hc
    cases hp with
    | cons st hp =>
      cases st with
      | ask g =>
        cases hc
        obtain ⟨hc', hok, he⟩ := ih hr hp (.run g)
        refine ⟨hc', okV_cons.2 ⟨trivial, hok⟩, ?_⟩
        simp [aOf, bOf, visMove] at he ⊢; exact he
      | ret g r =>
        cases hc
        obtain ⟨hc', hok, he⟩ := ih hr hp .idle
        refine ⟨hc', okV_cons.2 ⟨trivial, hok⟩, ?_⟩
        simp [aOf, bOf, visMove] at he ⊢; exact he
  | sync b _ ih =>
    intro h₀ h₁ x y hr hp hc
    cases hr with
    | cons hs hr =>
      cases hp with
      | cons st hp =>
        cases hs with
        | askE m =>
          cases st with
          | call g _ =>
            cases hc
            obtain ⟨hc', hok, he⟩ := ih hr hp (.waitE g m)
            refine ⟨hc', okV_cons.2 ⟨trivial, hok⟩, ?_⟩
            simp [aOf, bOf, visMove] at he ⊢; exact he
        | ansE m n hR =>
          cases st with
          | reply g _ _ =>
            cases hc
            obtain ⟨hc', hok, he⟩ := ih hr hp (.run g)
            refine ⟨hc', okV_cons.2 ⟨hR, hok⟩, ?_⟩
            simp [aOf, bOf, visMove] at he ⊢; exact he
        | askF m =>
          cases st with
          | call g _ =>
            cases hc
            obtain ⟨hc', hok, he⟩ := ih hr hp (.askF g m)
            refine ⟨hc', okV_cons.2 ⟨trivial, hok⟩, ?_⟩
            simp [aOf, bOf, visMove] at he ⊢; exact he
        | retF m n =>
          cases st with
          | reply g _ _ =>
            cases hc
            obtain ⟨hc', hok, he⟩ := ih hr hp (.run g)
            refine ⟨hc', okV_cons.2 ⟨trivial, hok⟩, ?_⟩
            simp [aOf, bOf, visMove] at he ⊢; exact he

/-- The host moves only visibly or in synchrony. -/
theorem zip_length {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) : s.length ≤ p.length + t.length := by
  induction h with
  | nil => exact le_rfl
  | left => simp; omega
  | right => simp; omega
  | sync => simp; omega

end Silmaril.Proofs.Games.Abstract.SessionHost

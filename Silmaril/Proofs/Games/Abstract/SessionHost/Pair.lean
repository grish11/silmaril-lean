module

public import Silmaril.Proofs.Games.Abstract.SessionHost.Host
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs
import Mathlib.Data.List.Induction

/-!
# The host beside copycat is a pairing (proofs)

`(hostDOn F R).pair (DStrategy.id F) = hostCopy F R`. A play of the pairing is tracked by the
state of `hostCopy` (`Inv`): the left half is a play of host moves, at a running position exactly
while a host call is answered; the right half is copycat on completed component calls, then the
call in progress (`ext`); while a component call is forwarded the current side is the right one.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost

universe u

variable {E F : Sig.{u}} {R : HostRel E}

/-- The events of completed calls. -/
def evs (cs : List (Call F)) : List (Ev F) := cs.flatMap fun x => [.ask x.1, .ans x.1 x.2]

theorem alternating_evs (cs : List (Call F)) {w : List (Ev F)} (hw : Ev.Alternating w) :
    Ev.Alternating (evs cs ++ w) := by
  induction cs with
  | nil => exact hw
  | cons x cs ih => exact .cons x.1 x.2 ih

@[simp] theorem evs_append (cs ds : List (Call F)) : evs (cs ++ ds) = evs cs ++ evs ds := by
  simp [evs]

@[simp] theorem double_append (w w' : List (Ev F)) :
    Ev.double (w ++ w') = Ev.double w ++ Ev.double w' := by
  simp [Ev.double]

/-- The copycat moves of the call in progress. -/
def ext : HSt E F → List (Move F F)
  | .askF m => [.inr (.ask m)]
  | .waitF m => [.inr (.ask m), .inl (.ask m)]
  | .ansF m n => [.inr (.ask m), .inl (.ask m), .inl (.ans m n)]
  | _ => []

/-- The position of the left half. -/
def lpos : HSt E F → Pos F E
  | .waitE m => .run m
  | _ => .idle

/-- The current side agrees with the state. -/
def SideOk : HSt E F → Bool → Prop
  | .idle, _ => True
  | .waitE _, b => b = false
  | _, b => b = true

/-- The invariant of a play of the pairing at a state of `hostCopy`. -/
structure Inv (R : HostRel E) (h : HSt E F) (p : List (Move F (E ⊕ₛ F))) : Prop where
  path : Path .idle p h.pos
  lmove : ∀ o ∈ (Split.halves false p).1, HostMove R o
  lpath : Path .idle (Split.halves false p).1 (lpos h)
  right : ∃ cs, (Split.halves false p).2 = Ev.double (evs cs) ++ ext h
  side : SideOk h (Split.side false p)

theorem side_append (b : Bool) (p q : List (Move F (E ⊕ₛ F))) :
    Split.side b (p ++ q) = Split.side (Split.side b p) q := by
  induction p generalizing b with
  | nil => rfl
  | cons x p ih =>
    rcases x with e | (q' | ⟨q', r⟩)
    · exact ih b
    · rcases q' with q' | q' <;> exact ih _
    · exact ih b

theorem inv_nil : Inv R (.idle : HSt E F) [] where
  path := .nil _
  lmove := fun _ h => nomatch h
  lpath := .nil _
  right := ⟨[], rfl⟩
  side := trivial

/-- **One step of `hostCopy` keeps the invariant.** -/
theorem Inv.step {h₀ h : HSt E F} {p : List (Move F (E ⊕ₛ F))} {o : Move F (E ⊕ₛ F)}
    (hi : Inv R h₀ p) (hs : HStep R h₀ o h) : Inv R h (p ++ [o]) := by
  obtain ⟨hp, hlm, hlp, ⟨cs, hr⟩, hside⟩ := hi
  obtain ⟨c₁, c₂⟩ := Split.halves_concat false p o
  have hp' : Path .idle (p ++ [o]) h.pos := hp.append (.single hs.pos)
  cases hs with
  | askE m =>
    refine ⟨hp', ?_, ?_, ⟨cs, ?_⟩, ?_⟩
    · rw [c₁]; simp only [Split.halves, List.mem_append, List.mem_singleton]
      rintro o (ho | rfl); exacts [hlm o ho, trivial]
    · rw [c₁]; simp only [Split.halves]; exact hlp.append (.single (.ask m))
    · rw [c₂]; simp [Split.halves, hr, ext]
    · rw [side_append]; rfl
  | ansE m n hR =>
    refine ⟨hp', ?_, ?_, ⟨cs, ?_⟩, ?_⟩
    · rw [c₁]; simp only [Split.halves, List.mem_append, List.mem_singleton]
      rintro o (ho | rfl); exacts [hlm o ho, hR]
    · rw [c₁]; simp only [Split.halves]; exact hlp.append (.single (.ret m n))
    · rw [c₂]; simp [Split.halves, hr, ext]
    · trivial
  | askF m =>
    refine ⟨hp', ?_, ?_, ⟨cs, ?_⟩, ?_⟩
    · rw [c₁]; simpa [Split.halves] using hlm
    · rw [c₁]; simpa [Split.halves, lpos] using hlp
    · rw [c₂]; simp [Split.halves, hr, ext]
    · rw [side_append]; rfl
  | fwdF m =>
    have hs : Split.side false p = true := hside
    refine ⟨hp', ?_, ?_, ⟨cs, ?_⟩, ?_⟩
    · rw [c₁, hs]; simpa [Split.halves] using hlm
    · rw [c₁, hs]; simpa [Split.halves, lpos] using hlp
    · rw [c₂, hs]; simp [Split.halves, hr, ext]
    · rw [side_append, hs]; rfl
  | replyF m n =>
    have hs : Split.side false p = true := hside
    refine ⟨hp', ?_, ?_, ⟨cs, ?_⟩, ?_⟩
    · rw [c₁, hs]; simpa [Split.halves] using hlm
    · rw [c₁, hs]; simpa [Split.halves, lpos] using hlp
    · rw [c₂, hs]; simp [Split.halves, hr, ext]
    · rw [side_append, hs]; rfl
  | retF m n =>
    refine ⟨hp', ?_, ?_, ⟨cs ++ [⟨m, n⟩], ?_⟩, trivial⟩
    · rw [c₁]; simpa [Split.halves] using hlm
    · rw [c₁]; simpa [Split.halves, lpos] using hlp
    · rw [c₂]; simp [Split.halves, hr, ext, evs, Ev.double]

theorem inv_of_hrun {h : HSt E F} {p : List (Move F (E ⊕ₛ F))} (hr : HRun R .idle p h) :
    Inv R h p := by
  induction p using List.reverseRecOn generalizing h with
  | nil => cases hr; exact inv_nil
  | append_singleton p o ih =>
    obtain ⟨h₀, h₁, h₂⟩ := hr.of_append
    cases h₂ with
    | cons hs hn => cases hn; exact (ih h₁).step hs

/-! ## Copycat prefixes -/

theorem double_prefix {cs : List (Call F)} {l : List (Move F F)} {w : List (Ev F)}
    (hw : Ev.Alternating w) (h : Ev.double (evs cs) ++ l <+: Ev.double w) :
    ∃ w', Ev.Alternating w' ∧ l <+: Ev.double w' := by
  induction cs generalizing w with
  | nil => exact ⟨w, hw, h⟩
  | cons x cs ih =>
    cases hw with
    | nil => exact absurd h.length_le (by simp [evs, Ev.double])
    | ask m => exact absurd h.length_le (by simp [evs, Ev.double])
    | cons m n hw =>
      simp only [evs, List.flatMap_cons, Ev.double, List.cons_append, List.nil_append,
        Ev.copy, List.cons_prefix_cons] at h
      exact ih hw (by simpa [evs, Ev.double] using h.2.2.2.2)

theorem copy_ask_ask {w : List (Ev F)} (hw : Ev.Alternating w) {m m' : F.Op}
    (h : [.inr (.ask m), .inl (.ask m')] <+: Ev.double w) : m' = m := by
  cases hw with
  | nil => exact absurd h.length_le (by simp)
  | ask μ => simp [Ev.double] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | cons μ ν _ =>
    simp only [Ev.double_cons, Ev.copy_ask, Ev.copy_ans, List.cons_append, List.nil_append,
      List.cons_prefix_cons, Sum.inr.injEq, Sum.inl.injEq, Ev.ask.injEq] at h
    rw [h.2.1, h.1]

theorem copy_ask_ret {w : List (Ev F)} (hw : Ev.Alternating w) {m : F.Op} {r : F.Ar m}
    (h : [.inr (.ask m), .inr (.ans m r)] <+: Ev.double w) : False := by
  cases hw with
  | nil => exact absurd h.length_le (by simp)
  | ask μ => simp [Ev.double] at h
  | cons μ ν _ =>
    simp only [Ev.double_cons, Ev.copy_ask, Ev.copy_ans, List.cons_append, List.nil_append,
      List.cons_prefix_cons] at h
    exact nomatch h.2.1

theorem copy_ans_ask {w : List (Ev F)} (hw : Ev.Alternating w) {m m' : F.Op} {n : F.Ar m}
    (h : [.inr (.ask m), .inl (.ask m), .inl (.ans m n), .inl (.ask m')] <+: Ev.double w) :
    False := by
  cases hw with
  | nil => exact absurd h.length_le (by simp)
  | ask μ => exact absurd h.length_le (by simp [Ev.double])
  | cons μ ν _ =>
    simp only [Ev.double_cons, Ev.copy_ask, Ev.copy_ans, List.cons_append, List.nil_append,
      List.cons_prefix_cons] at h
    exact nomatch h.2.2.2.1

theorem copy_ans_ret {w : List (Ev F)} (hw : Ev.Alternating w) {m : F.Op} {n r : F.Ar m}
    (h : [.inr (.ask m), .inl (.ask m), .inl (.ans m n), .inr (.ans m r)] <+: Ev.double w) :
    r = n := by
  cases hw with
  | nil => exact absurd h.length_le (by simp)
  | ask μ => exact absurd h.length_le (by simp [Ev.double])
  | cons μ ν _ =>
    simp only [Ev.double_cons, Ev.copy_ask, Ev.copy_ans, List.cons_append, List.nil_append,
      List.cons_prefix_cons, Sum.inr.injEq, Sum.inl.injEq, Ev.ask.injEq, Ev.ans.injEq] at h
    obtain ⟨rfl, -, ⟨-, h₁⟩, ⟨-, h₂⟩, -⟩ := h
    exact eq_of_heq (h₂.trans h₁.symm)

/-! ## The plays of the pairing -/

/-- The pairing, at the level of finite plays. -/
abbrev pairS (F : Sig.{u}) (R : HostRel E) : Strategy F (E ⊕ₛ F) :=
  (hostOnS F R).pair (Strategy.id F)

/-- **A play of the pairing extends by a move of `hostCopy`.** -/
theorem Inv.hstep {h₀ : HSt E F} {p : List (Move F (E ⊕ₛ F))} {o : Move F (E ⊕ₛ F)}
    (hi : Inv R h₀ p) (hm : p ++ [o] ∈ pairS F R) : ∃ h, HStep R h₀ o h := by
  obtain ⟨⟨z, hz⟩, ⟨-, hl⟩, ⟨w, hw, hpw⟩⟩ := hm
  obtain ⟨x, hx, hst⟩ := Path.concat_iff.1 hz
  cases hi.path.det hx
  obtain ⟨c₁, c₂⟩ := Split.halves_concat false p o
  obtain ⟨cs, hr⟩ := hi.right
  rw [c₁] at hl
  rw [c₂, hr] at hpw
  have hside := hi.side
  cases h₀ with
  | idle =>
    cases hst with
    | ask q => rcases q with m | m; exacts [⟨_, .askE m⟩, ⟨_, .askF m⟩]
  | waitE m =>
    have hs : Split.side false p = false := hside
    cases hst with
    | call _ m' => rw [hs] at hl; exact absurd (hl (.inl (.ask m')) (by simp [Split.halves])) id
    | ret _ r => exact ⟨_, .ansE m r (hl (.inr (.ans m r)) (by simp [Split.halves]))⟩
  | askF m =>
    have hs : Split.side false p = true := hside
    rw [hs] at hpw
    obtain ⟨w', hw', hp'⟩ := double_prefix hw (List.append_assoc _ _ _ ▸ hpw)
    cases hst with
    | call _ m' =>
      simp only [ext, Split.halves, List.singleton_append] at hp'
      cases copy_ask_ask hw' hp'
      exact ⟨_, .fwdF m⟩
    | ret _ r =>
      simp only [ext, Split.halves, List.singleton_append] at hp'
      exact (copy_ask_ret hw' hp').elim
  | waitF m =>
    cases hst with
    | reply _ _ n => exact ⟨_, .replyF m n⟩
  | ansF m n =>
    have hs : Split.side false p = true := hside
    rw [hs] at hpw
    obtain ⟨w', hw', hp'⟩ := double_prefix hw (List.append_assoc _ _ _ ▸ hpw)
    cases hst with
    | call _ m' =>
      simp only [ext, Split.halves, List.cons_append, List.nil_append] at hp'
      exact (copy_ans_ask hw' hp').elim
    | ret _ r =>
      simp only [ext, Split.halves, List.cons_append, List.nil_append] at hp'
      cases copy_ans_ret hw' hp'
      exact ⟨_, .retF m n⟩

theorem Inv.mem {h : HSt E F} {p : List (Move F (E ⊕ₛ F))} (hi : Inv R h p) : p ∈ pairS F R := by
  obtain ⟨hp, hlm, hlp, ⟨cs, hr⟩, -⟩ := hi
  refine ⟨⟨_, hp⟩, ⟨⟨_, hlp⟩, hlm⟩, ?_⟩
  rw [hr]
  cases h with
  | idle => exact ⟨_, alternating_evs cs .nil, by simp [ext]⟩
  | waitE m => exact ⟨_, alternating_evs cs .nil, by simp [ext]⟩
  | askF m =>
    exact ⟨_, alternating_evs cs (.ask m), by simp [ext, Ev.double]⟩
  | waitF m =>
    exact ⟨_, alternating_evs cs (.ask m), by simp [ext, Ev.double]⟩
  | ansF m n =>
    exact ⟨_, alternating_evs cs (.cons m n .nil),
      ⟨[.inr (.ans m n)], by simp [ext, Ev.double]⟩⟩

theorem mem_pairS_iff {p : List (Move F (E ⊕ₛ F))} :
    p ∈ pairS F R ↔ ∃ h, HRun R .idle p h := by
  constructor
  · intro hp
    induction p using List.reverseRecOn with
    | nil => exact ⟨_, .nil _⟩
    | append_singleton p o ih =>
      obtain ⟨h₀, hr⟩ := ih ((pairS F R).of_prefix hp (List.prefix_append _ _))
      obtain ⟨h, hs⟩ := (inv_of_hrun hr).hstep hp
      exact ⟨h, hr.append (.single hs)⟩
  · rintro ⟨h, hr⟩
    exact (inv_of_hrun hr).mem

/-- **The host beside copycat is the pairing of the host on `F` with copycat.** -/
theorem pair_eq : (hostDOn F R).pair (DStrategy.id F) = hostCopy F R := by
  have hpl : ((hostDOn F R).pair (DStrategy.id F)).toStrategy = (hostCopy F R).toStrategy :=
    Strategy.ext fun _ => mem_pairS_iff
  refine DStrategy.ext hpl (Set.ext fun p => ⟨?_, ?_⟩) (Set.ext fun I => ⟨?_, ?_⟩)
  · rintro ⟨hp, ⟨-, m, hm, hd⟩ | h⟩
    · obtain ⟨h, hr⟩ := mem_pairS_iff.1 hp
      have hl := (inv_of_hrun hr).lpath.det hm
      cases h <;> simp [lpos] at hl
      cases hl
      exact ⟨_, hr, hd⟩
    · exact h.elim
  · rintro ⟨m, hr, hd⟩
    have hi := inv_of_hrun hr
    exact ⟨hi.mem, .inl ⟨hi.mem.2.1, m, hi.lpath, hd⟩⟩
  · rintro ⟨hI, hsub, -, -⟩
    exact ⟨hI, fun p hp => mem_pairS_iff.1 (hsub hp)⟩
  · rintro ⟨hI, hsub⟩
    have hsub' : I ⊆ (pairS F R).plays := fun p hp => mem_pairS_iff.2 (hsub hp)
    refine ⟨hI, hsub', fun hL => ⟨hL, ?_⟩, fun hR => ⟨hR, ?_⟩⟩
    · rintro x ⟨p, hp, hx⟩
      exact (hostOnS F R).of_prefix (hsub' hp).2.1 hx
    · rintro x ⟨p, hp, hx⟩
      exact (Strategy.id F).of_prefix (hsub' hp).2.2 hx

end Silmaril.Proofs.Games.Abstract.SessionHost

module

public import Silmaril.Wasm.Component.OutOfRange.Defs
public import Silmaril.Wasm.Component.DWiringLaws.Thms
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# Trap propagation excludes trap chatter

* `not_legal_lower_ask_ask`, `not_legal_upper_ask_ask`,
  `not_legal_upper_ans_ans`: the alternation of the game.
* `no_trap_tail`: a trap-propagating strategy has no infinite play that, from
  some member on, moves only below and receives only `none`. Three moves after
  that member contain a lower answer `none` followed by a lower move (two
  lower questions in a row are illegal), which trap propagation forbids.
* `ofHandler_ask_ans`: in a play of a handler, a question answered at once
  (with no call in between) is answered by the handler's `pure` program.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.OutOfRange

open Silmaril.Games Silmaril.Wasm.Component

universe u

/-- Two lower questions in a row are illegal. -/
theorem not_legal_lower_ask_ask {E F : Sig.{u}} {s : List (Move E F)} {m m' : E.Op} :
    ¬ Legal (s ++ [.inl (.ask m), .inl (.ask m')]) := by
  rintro ⟨y, h⟩
  obtain ⟨x, -, h⟩ := Path.append_iff.1 h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ _ => cases h₁; cases h₂

/-- Two upper questions in a row are illegal. -/
theorem not_legal_upper_ask_ask {E F : Sig.{u}} {s : List (Move E F)} {q q' : F.Op} :
    ¬ Legal (s ++ [.inr (.ask q), .inr (.ask q')]) := by
  rintro ⟨y, h⟩
  obtain ⟨x, -, h⟩ := Path.append_iff.1 h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ _ => cases h₁; cases h₂

/-- Two upper answers in a row are illegal. -/
theorem not_legal_upper_ans_ans {E F : Sig.{u}} {s : List (Move E F)} {q q' : F.Op}
    {r : F.Ar q} {r' : F.Ar q'} : ¬ Legal (s ++ [.inr (.ans q r), .inr (.ans q' r')]) := by
  rintro ⟨y, h⟩
  obtain ⟨x, -, h⟩ := Path.append_iff.1 h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ _ => cases h₁; cases h₂

variable {O : Type} {G : Sig.{0}}

/-- **No trap tail.** A trap-propagating strategy has no infinite play that,
after a member `t₀`, only moves below and only receives the answer `none`. -/
theorem no_trap_tail {σ : DStrategy (sigO O) G} (hσ : TrapPropagating σ)
    {I : Set (List (Move (sigO O) G))} (hI : I ∈ σ.inf) {t₀ : List (Move (sigO O) G)}
    (ht₀ : t₀ ∈ I)
    (htr : ∀ w x, t₀ ++ w ++ [x] ∈ I →
      ∃ e : Ev (sigO O), x = .inl e ∧ ∀ m r, e = .ans m r → r = none) : False := by
  have hP := σ.inf_isInf hI
  obtain ⟨s, hs, hl⟩ := hP.unbounded (t₀.length + 3)
  obtain ⟨v, rfl⟩ := hP.prefix_of_length_le ht₀ hs (by omega)
  have hv : 3 ≤ v.length := by simp at hl; omega
  have hpl : ∀ u, u <+: t₀ ++ v → u ∈ σ.toStrategy := fun u hu =>
    σ.inf_sub hI (hP.of_prefix hs hu)
  match v, hv, hs, hpl with
  | a :: b :: c :: rest, _, hs, hpl =>
    have mem : ∀ u, u <+: t₀ ++ a :: b :: c :: rest → u ∈ I := fun u hu =>
      hP.of_prefix hs hu
    obtain ⟨ea, rfl, hea⟩ := htr [] a (mem _ ⟨b :: c :: rest, by simp⟩)
    obtain ⟨eb, rfl, heb⟩ := htr [.inl ea] b (mem _ ⟨c :: rest, by simp⟩)
    obtain ⟨ec, rfl, -⟩ := htr [.inl ea, .inl eb] c (mem _ ⟨rest, by simp⟩)
    cases ea with
    | ans m r =>
      obtain rfl := hea m r rfl
      obtain ⟨g, hg⟩ := hσ t₀ m (.inl eb) (hpl _ ⟨.inl ec :: rest, by simp⟩)
      cases hg
    | ask m =>
      cases eb with
      | ask m' =>
        exact not_legal_lower_ask_ask (s := t₀) (m := m) (m' := m')
          (σ.toStrategy.legal (hpl _ ⟨.inl ec :: rest, by simp⟩))
      | ans m' r' =>
        obtain rfl := heb m' r' rfl
        obtain ⟨g, hg⟩ := hσ (t₀ ++ [.inl (.ask m)]) m' (.inl ec) (hpl _ ⟨rest, by simp⟩)
        cases hg

/-- An eventually-trap infinite play has a trap tail. -/
theorem not_eventuallyTrap {n : Nat} {σ : DStrategy sigU G} (hσ : TrapPropagating σ)
    {I : Set (List (Move sigU G))} (hI : I ∈ σ.inf) : ¬ EventuallyTrap n I := by
  rintro ⟨t₀, ht₀, htr⟩
  refine no_trap_tail hσ hI ht₀ fun w x hx => ?_
  obtain ⟨e, rfl, he⟩ := htr w x hx
  exact ⟨e, rfl, fun m r h => by subst h; exact he⟩

/-- Trap chatter has a trap tail. -/
theorem not_trapChatter {n : Nat} {σ : DStrategy sigU G} (hσ : TrapPropagating σ)
    {s : List (Move (sigN n) G)} : ¬ TrapChatter n σ s := by
  rintro ⟨I, hI, t₀, ht₀, -, htr, -⟩
  refine no_trap_tail hσ hI ht₀ fun w x hx => ?_
  obtain ⟨e, rfl, he⟩ := htr w x hx
  exact ⟨e, rfl, fun m r h => by subst h; exact he⟩

/-- Silent chatter below a trap-silent handler has a trap tail. -/
theorem not_silentChatter {E : Sig.{0}} {h : Handler E (sigO O)} (hh : TrapSilent h)
    {σ : DStrategy (sigO O) G} (hσ : TrapPropagating σ) {s : List (Move E G)} :
    ¬ SilentChatter h σ s := by
  rintro ⟨I, hI, t₀, ht₀, -, htr, -⟩
  refine no_trap_tail hσ hI ht₀ fun w x hx => ?_
  obtain ⟨e, rfl, he⟩ := htr w x hx
  exact ⟨e, rfl, fun m r h' => by subst h'; exact hh m r he⟩

/-- Runs of a handler without visible moves stay put. -/
theorem handler_run_nil {E F : Sig.{u}} {h : Handler E F} {x y : h.toReduction.toLTS.State}
    (hr : h.toReduction.toLTS.Run x [] y) : x = y := by
  cases hr with
  | nil => rfl
  | tau hs _ =>
    cases hs with
    | tau hc => exact hc.elim

/-- **A question answered at once is answered by a `pure` program.** -/
theorem ofHandler_ask_ans {E : Sig.{0}} {h : Handler E (sigO O)}
    {s : List (Move E (sigO O))} {q q' : O} {r : Option Payload}
    (hs : s ++ [.inr (.ask q), .inr (.ans q' r)] ∈ Strategy.ofHandler h) :
    q' = q ∧ h q = .pure r := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hs
  obtain ⟨y₁, -, hy⟩ := LTS.Run.of_append hy
  obtain ⟨x₁, x₂, h₀, h₁, hy⟩ := LTS.Run.cons_inv hy
  obtain ⟨x₃, x₄, h₂, h₃, -⟩ := LTS.Run.cons_inv hy
  cases handler_run_nil h₀
  cases h₁ with
  | ask =>
    cases handler_run_nil h₂
    cases h₃ with
    | ret hd => exact ⟨rfl, hd⟩

end Silmaril.Proofs.Wasm.Component.OutOfRange

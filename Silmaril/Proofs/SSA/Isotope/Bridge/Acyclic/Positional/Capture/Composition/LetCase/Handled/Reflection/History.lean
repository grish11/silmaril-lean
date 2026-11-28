module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Isotope.Semantics (InstructionModel)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event Structured.toSmall
  Structured.request_eq_of_vis_eq Structured.vis_eq_iff Structured.eval_bind_of_not_pure)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {X Y : Type 1}

local notation "Value" => LetCase.Structural.Finite.Value

private theorem of_mul_cancel {α : Type} {a b : α} {x y : FreeMonoid α}
    (same : FreeMonoid.of a * x = FreeMonoid.of b * y) : a = b ∧ x = y := by
  have lists := congrArg FreeMonoid.toList same
  rw [FreeMonoid.toList_of_mul, FreeMonoid.toList_of_mul] at lists
  exact ⟨(List.cons.inj lists).1, FreeMonoid.ext (List.cons.inj lists).2⟩

theorem history_one_proof (x : X) : history (1 : Log Empty Φ) x = .result x := rfl

theorem history_cons_proof (f : Φ) (argument : Value (instrSrc f)) (reply : Value (instrTrg f))
    (log : Log Empty Φ) (x : X) :
    history (FreeMonoid.of ⟨f, argument, reply⟩ * log) x =
      .exchange (.call f argument) reply (history log x) := rfl

theorem hasTrace_ret_history_proof (x y : X) (log : Log Empty Φ) :
    HasTrace (ret x : Tree (Events Φ) X) (history log y) ↔ log = 1 ∧ x = y := by
  induction log using FreeMonoid.inductionOn' with
  | one =>
    change out (ret x : Tree (Events Φ) X) = Part.some (.ret y) ↔ _
    rw [out_ret]
    exact ⟨fun same => ⟨rfl, Visible.ret.inj (Part.some_injective same)⟩, fun same => by rw [same.2]⟩
  | of_mul exchange log _ =>
    obtain ⟨f, argument, reply⟩ := exchange
    rw [history_cons_proof]
    constructor
    · rintro ⟨k, root, -⟩
      rw [out_ret] at root
      cases Part.some_injective root
    · rintro ⟨impossible, -⟩
      cases impossible

theorem hasTrace_vis_history_proof (f : Φ) (argument : Value (instrSrc f))
    (k : Value (instrTrg f) → Tree (Events Φ) X) (log : Log Empty Φ) (y : X) :
    HasTrace (vis (.call f argument) k) (history log y) ↔
      ∃ reply rest, log = FreeMonoid.of ⟨f, argument, reply⟩ * rest ∧ HasTrace (k reply) (history rest y) := by
  induction log using FreeMonoid.inductionOn' with
  | one =>
    constructor
    · intro root
      change out (vis (Structured.Event.call f argument) k) = Part.some (.ret y) at root
      rw [out_vis] at root
      cases Part.some_injective root
    · rintro ⟨reply, rest, impossible, -⟩
      cases impossible
  | of_mul exchange log _ =>
    obtain ⟨g, sent, answer⟩ := exchange
    rw [history_cons_proof]
    constructor
    · rintro ⟨l, root, tail⟩
      have tree : vis (Structured.Event.call f argument) k = vis (.call g sent) l :=
        out_injective (root.trans (out_vis _ _).symm)
      cases Structured.request_eq_of_vis_eq Atoms tree
      have same := ((Structured.vis_eq_iff Atoms).mp tree).2 answer
      exact ⟨answer, log, rfl, same ▸ tail⟩
    · rintro ⟨reply, rest, same, tail⟩
      obtain ⟨exchange, rfl⟩ := of_mul_cancel same
      cases exchange
      exact ⟨k, out_vis _ _, tail⟩

theorem hasTrace_bind_history_proof (t : Tree (Events Φ) X) (k : X → Tree (Events Φ) Y)
    (log : Log Empty Φ) (y : Y) :
    HasTrace (t >>= k) (history log y) ↔
      ∃ x first rest, HasTrace t (history first x) ∧ HasTrace (k x) (history rest y) ∧
        first * rest = log := by
  constructor
  · intro seen
    induction log using FreeMonoid.inductionOn' generalizing t with
    | one =>
      rcases cases_visible t with rfl | ⟨x, rfl⟩ | ⟨R, e, l, rfl⟩
      · rw [diverge_bind] at seen
        cases (hasTrace_diverge_iff _).mp seen
      · exact ⟨x, 1, 1, (hasTrace_ret_history_proof x x 1).mpr ⟨rfl, rfl⟩, (pure_bind x k) ▸ seen, rfl⟩
      · cases e with
        | call f argument =>
          rw [vis_bind] at seen
          obtain ⟨_, _, impossible, -⟩ := (hasTrace_vis_history_proof f argument _ 1 y).mp seen
          cases impossible
    | of_mul exchange log ih =>
      rcases cases_visible t with rfl | ⟨x, rfl⟩ | ⟨R, e, l, rfl⟩
      · rw [diverge_bind] at seen
        obtain ⟨f, argument, reply⟩ := exchange
        cases (hasTrace_diverge_iff _).mp seen
      · exact ⟨x, 1, _, (hasTrace_ret_history_proof x x 1).mpr ⟨rfl, rfl⟩, (pure_bind x k) ▸ seen, one_mul _⟩
      · cases e with
        | call f argument =>
          rw [vis_bind] at seen
          obtain ⟨reply, rest, same, tail⟩ := (hasTrace_vis_history_proof f argument _ _ y).mp seen
          obtain ⟨exchange, rfl⟩ := of_mul_cancel same
          cases exchange
          obtain ⟨x, first, rest, left, right, joined⟩ := ih (l reply) tail
          exact ⟨x, FreeMonoid.of ⟨f, argument, reply⟩ * first, rest,
            (hasTrace_vis_history_proof f argument l _ x).mpr ⟨reply, first, rfl, left⟩, right,
            by rw [mul_assoc, joined]⟩
  · rintro ⟨x, first, rest, left, right, rfl⟩
    induction first using FreeMonoid.inductionOn' generalizing t with
    | one =>
      have root : t = ret x := out_injective (left.trans (out_ret x).symm)
      rw [root, one_mul]
      exact (pure_bind x k).symm ▸ right
    | of_mul exchange first ih =>
      obtain ⟨f, argument, reply⟩ := exchange
      obtain ⟨l, root, tail⟩ := left
      have shape : t = vis (.call f argument) l := out_injective (root.trans (out_vis _ _).symm)
      rw [shape, vis_bind, mul_assoc]
      exact (hasTrace_vis_history_proof f argument _ _ y).mpr ⟨reply, _, rfl, ih (l reply) tail⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

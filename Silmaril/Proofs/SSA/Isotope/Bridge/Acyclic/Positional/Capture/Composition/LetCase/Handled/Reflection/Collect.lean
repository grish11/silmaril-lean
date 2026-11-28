module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Defs
public import Silmaril.Semantics.NondeterministicTrace.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.History

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Silmaril.Semantics.NondeterministicTrace (Finite)
open Isotope.Semantics (BoundEnv InstructionModel)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀ run)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall Structured.eval_bind_of_not_pure)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {X Y : Type 1} {S T : Type}

local notation "Value" => LetCase.Structural.Finite.Value
local notation "Outcomes" => LetSeq.StraightLine.Structural.Trace Empty Φ
local notation "small" => Structured.toSmall Atoms

/-- The complete histories of a tree, as outcomes of the ordered trace
monad. Results are read through an equivalence to the event universe. -/
def collect (e : X ≃ S) (t : Tree (Events Φ) X) : Outcomes S :=
  Finite.ofOutcomes {p | HasTrace t (history p.2 (e.symm p.1))}

theorem mem_collect (e : X ≃ S) (t : Tree (Events Φ) X) (s : S) (log : Log Empty Φ) :
    (s, log) ∈ (collect e t).outcomes ↔ HasTrace t (history log (e.symm s)) :=
  Iff.rfl

theorem collect_pure (e : X ≃ S) (x : X) : collect (Φ := Φ) e (pure x) = pure (e x) := by
  apply Finite.outcomes_injective
  ext ⟨s, log⟩
  change HasTrace (ret x) (history log (e.symm s)) ↔ (s, log) = (e x, 1)
  rw [hasTrace_ret_history_proof, Prod.mk.injEq, Equiv.eq_symm_apply]
  exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩

theorem collect_bind (e : X ≃ S) (e' : Y ≃ T) (t : Tree (Events Φ) X) (k : X → Tree (Events Φ) Y) :
    collect e' (t >>= k) = (collect e t >>= fun s => collect e' (k (e.symm s))) := by
  apply Finite.outcomes_injective
  ext ⟨s, log⟩
  rw [Finite.mem_bind]
  change HasTrace (t >>= k) (history log (e'.symm s)) ↔ _
  rw [hasTrace_bind_history_proof]
  constructor
  · rintro ⟨x, first, rest, left, right, joined⟩
    exact ⟨e x, first, rest, by simpa only [collect, Finite.outcomes_ofOutcomes, Set.mem_ofPred_eq,
      Equiv.symm_apply_apply] using left, by simpa only [collect, Finite.outcomes_ofOutcomes,
      Set.mem_ofPred_eq, Equiv.symm_apply_apply] using right, joined⟩
  · rintro ⟨a, first, rest, left, right, joined⟩
    exact ⟨e.symm a, first, rest, left, right, joined⟩

theorem model_eval_bind_proof (f : Φ) (x : Val (instrSrc f)) (k : Val (instrTrg f) → Tree (Events Φ) X) :
    ((model Φ).eval f x >>= k) =
      vis (.call f (small (instrSrc f) x)) (fun reply => k ((small (instrTrg f)).symm reply)) :=
  Structured.eval_bind_of_not_pure Atoms noPure (fun pure => Bool.noConfusion pure) x k

theorem collect_eval (f : Φ) (x : Val (instrSrc f)) :
    collect (small (instrTrg f)) ((model Φ).eval f x) =
      LetSeq.StraightLine.Structural.model.eval f (small (instrSrc f) x) := by
  apply Finite.outcomes_injective
  ext ⟨s, log⟩
  change HasTrace ((model Φ).eval f x) (history log ((small (instrTrg f)).symm s)) ↔
    (s, log) ∈ Set.range fun y : Value (instrTrg f) => (y, FreeMonoid.of ⟨f, small (instrSrc f) x, y⟩)
  rw [← bind_pure ((model Φ).eval f x), model_eval_bind_proof, hasTrace_vis_history_proof]
  constructor
  · rintro ⟨reply, rest, rfl, tail⟩
    obtain ⟨rfl, same⟩ := (hasTrace_ret_history_proof _ _ _).mp tail
    rw [(small (instrTrg f)).symm.injective same, mul_one]
    exact ⟨s, rfl⟩
  · rintro ⟨y, same⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨y, 1, (mul_one _).symm, (hasTrace_ret_history_proof _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- Raise every slot of an event environment to the tree universe. -/
def raise {n : Nat} {β : Context n} (ρ : BoundEnv Value β) : BoundEnv Val β :=
  fun i => (small (β.get i)).symm (ρ i)

theorem lower_raise {n : Nat} {β : Context n} (ρ : BoundEnv Value β) : lower (raise ρ) = ρ :=
  funext fun _ => Equiv.apply_symm_apply _ _

theorem lower_snoc {n : Nat} {β : Context n} {A : Ty Empty} (ρ : BoundEnv Val β) (x : Val A) :
    lower (ρ.snoc x) = (lower ρ).snoc (small A x) :=
  funext (Fin.cases rfl (fun _ => rfl))

set_option backward.isDefEq.respectTransparency false in
/-- The ordered trace semantics is the set of complete histories of the
free tree semantics. -/
theorem collect_denote {n : Nat} {β : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty Empty}
    (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Val β) :
    collect (small A) (d.denote Val (model Φ) (fun x => x.elim) ρ) = run d (lower ρ) := by
  induction d with
  | fv h => rename_i x _; exact x.elim
  | bv => exact collect_pure _ _
  | unit => exact collect_pure _ _
  | op ha ih =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ih]
    exact bind_congr fun s => (collect_eval _ _).trans (by rw [Equiv.apply_symm_apply])
  | let₁ ha hb iha ihb =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [iha]
    exact bind_congr fun s => (ihb _).trans (by rw [lower_snoc, Equiv.apply_symm_apply]; rfl)
  | pair ha hb iha ihb =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [iha]
    refine bind_congr fun s => ?_
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ihb]
    exact bind_congr fun s' => (collect_pure _ _).trans
      (congrArg pure (Prod.ext (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)))
  | let₂ ha hc iha ihc =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [iha]
    refine bind_congr fun s => (ihc _).trans (congrArg (run hc) ?_)
    obtain ⟨s₁, s₂⟩ := s
    rw [lower_snoc, lower_snoc]
    exact congrArg₂ (fun u v => ((lower ρ).snoc u).snoc v) (Equiv.apply_symm_apply _ _)
      (Equiv.apply_symm_apply _ _)
  | inl ha ih =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ih]
    exact bind_congr fun s => (collect_pure _ _).trans
      (congrArg pure (congrArg Sum.inl (Equiv.apply_symm_apply _ _)))
  | inr ha ih =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ih]
    exact bind_congr fun s => (collect_pure _ _).trans
      (congrArg pure (congrArg Sum.inr (Equiv.apply_symm_apply _ _)))
  | case he hl hr ihe ihl ihr =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ihe]
    refine bind_congr fun s => ?_
    cases s with
    | inl a => exact (ihl _).trans (by rw [lower_snoc, Equiv.apply_symm_apply]; rfl)
    | inr b => exact (ihr _).trans (by rw [lower_snoc, Equiv.apply_symm_apply]; rfl)
  | abort ha ih =>
    refine (collect_bind (small _) (small _) _ _).trans ?_
    rw [ih]
    exact bind_congr fun s => nomatch s

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

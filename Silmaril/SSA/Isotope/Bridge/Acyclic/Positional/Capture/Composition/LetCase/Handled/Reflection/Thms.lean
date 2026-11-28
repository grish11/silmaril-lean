module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.History
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Collect
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Faithful

/-! # Handled traces of the free interpretation reflect native equations

The primitive interpretation is the free one: every primitive is a request
with its typed argument, answered at its declared result type. The older
context is structural, as in the native reflection theorem it relies on.

Two captured operands that are not natively equal have a complete finite
history, at some packed input, that one of them shows and the other does
not. A reply policy that can replay every complete history therefore gives
a faithful semantic functor. The permissive policy and the scripted policy
are of this kind. A policy that cannot replay some history may identify
different native classes.

Nothing here concerns cyclic terms, other signatures, or refinement of
machine traces.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Isotope.Semantics (BoundEnv ProductModel)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀ run)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u w s

/-- For a fixed older environment, the packed value determines the input. -/
theorem wrapValue_injective {τ : Type u} [TypeFormers τ] {D : τ → Type w} [ProductModel D]
    {n : Nat} (β : BoundCtx τ n) {X : τ} (ρ : BoundEnv D β) :
    Function.Injective (wrapValue (X := X) β ρ) :=
  wrapValue_injective_proof β ρ

namespace Free

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat} {β : Context d} {A B : Ty Empty}

local notation "Value" => LetCase.Structural.Finite.Value
local notation "small" => Structured.toSmall Atoms
local notation "⟪" d "⟫" => Derivation.denote Val (model Φ) d (fun x => Empty.elim x)

/-! ## Complete histories of free trees -/

section Histories

variable {X Y : Type 1}

@[simp] theorem history_one (x : X) : history (1 : Log Empty Φ) x = .result x := rfl

@[simp] theorem history_cons (f : Φ) (argument : Value (instrSrc f)) (reply : Value (instrTrg f))
    (log : Log Empty Φ) (x : X) :
    history (FreeMonoid.of ⟨f, argument, reply⟩ * log) x =
      .exchange (.call f argument) reply (history log x) := rfl

theorem history_map (g : X → Y) (log : Log Empty Φ) (x : X) :
    (history log x).map g = history log (g x) :=
  history_map_proof g log x

/-- A return shows only the empty history, at its own value. -/
theorem hasTrace_ret_history (x y : X) (log : Log Empty Φ) :
    HasTrace (ret x : Tree (Events Φ) X) (history log y) ↔ log = 1 ∧ x = y :=
  hasTrace_ret_history_proof x y log

/-- A request shows the histories that begin with an exchange at that
request and continue in the continuation of the reply. -/
theorem hasTrace_vis_history (f : Φ) (argument : Value (instrSrc f))
    (k : Value (instrTrg f) → Tree (Events Φ) X) (log : Log Empty Φ) (y : X) :
    HasTrace (vis (.call f argument) k) (history log y) ↔
      ∃ reply rest, log = FreeMonoid.of ⟨f, argument, reply⟩ * rest ∧ HasTrace (k reply) (history rest y) :=
  hasTrace_vis_history_proof f argument k log y

/-- A complete history of a sequence splits at the intermediate return. -/
theorem hasTrace_bind_history (t : Tree (Events Φ) X) (k : X → Tree (Events Φ) Y)
    (log : Log Empty Φ) (y : Y) :
    HasTrace (t >>= k) (history log y) ↔
      ∃ x first rest, HasTrace t (history first x) ∧ HasTrace (k x) (history rest y) ∧
        first * rest = log :=
  hasTrace_bind_history_proof t k log y

/-- Each primitive is one request, continued at the raised reply. -/
theorem model_eval_bind (f : Φ) (x : Val (instrSrc f)) (k : Val (instrTrg f) → Tree (Events Φ) X) :
    ((model Φ).eval f x >>= k) =
      vis (.call f (small (instrSrc f) x)) (fun reply => k ((small (instrTrg f)).symm reply)) :=
  model_eval_bind_proof f x k

end Histories

/-- The outcomes of the ordered trace semantics are the complete histories
of the free tree semantics, in every environment. -/
theorem mem_run_iff {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : Derivation Φ Γ₀ γ t A) (ρ : BoundEnv Val γ) (result : Value A) (log : Log Empty Φ) :
    (result, log) ∈ (run d (lower ρ)).outcomes ↔ HasTrace (⟪d⟫ ρ) (history log ((small A).symm result)) :=
  mem_run_iff_proof d ρ result log

/-! ## Policies that replay every history -/

theorem permissive_exposes : Exposes (permissive Φ) :=
  permissive_exposes_proof

/-- The scripted policy replays a history from the state that lists it. -/
theorem scripted_replay {X : Type 1} (log : Log Empty Φ) (result : X) :
    Replay (scripted Φ) log (history log result) :=
  scripted_replay_proof log result

theorem scripted_exposes : Exposes (scripted Φ) :=
  fun log result => ⟨log, scripted_replay log result⟩

/-! ## Reflection on packed operands -/

/-- Operands with the same complete histories at every packed input are
natively equal. -/
theorem equiv_of_histories (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B)
    (same : ∀ (w : Val (wrap β A)) (log : Log Empty Φ) (y : Val (wrap β B)),
      HasTrace ((pack β a).run (model Φ) w) (history log y) ↔
        HasTrace ((pack β b).run (model Φ) w) (history log y)) :
    Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  equiv_of_histories_proof input a b same

/-- Operands that are not natively equal are separated by one complete
finite history at one packed input. -/
theorem exists_separating_history (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B)
    (differ : ¬ Equiv false Γ₀ (β.snoc A) a.1 b.1 B) :
    ∃ (w : Val (wrap β A)) (log : Log Empty Φ) (y : Val (wrap β B)),
      ¬ (HasTrace ((pack β a).run (model Φ) w) (history log y) ↔
        HasTrace ((pack β b).run (model Φ) w) (history log y)) := by
  by_contra none
  exact differ (equiv_of_histories input a b fun w log y => by
    by_contra bad
    exact none ⟨w, log, y, bad⟩)

/-- Natively equal operands have equal packed trees. -/
theorem run_pack_eq_of_equiv {a b : Operand Φ (β.snoc A) B}
    (h : Equiv false Γ₀ (β.snoc A) a.1 b.1 B) (w : Val (wrap β A)) :
    (pack β a).run (model Φ) w = (pack β b).run (model Φ) w :=
  run_pack_eq_of_equiv_proof h w

/-- Native equality of captured operands is equality of their packed free
trees at every packed input. -/
theorem equiv_iff_run_pack_eq (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    Equiv false Γ₀ (β.snoc A) a.1 b.1 B ↔
      ∀ w : Val (wrap β A), (pack β a).run (model Φ) w = (pack β b).run (model Φ) w :=
  ⟨fun h w => run_pack_eq_of_equiv h w,
    fun same => equiv_of_histories input a b fun w log y => by rw [same w]⟩

variable {State : Type s}

/-- Mutual handled-trace inclusion of the packed programs, at a policy
that replays every complete history, gives native equality. -/
theorem equiv_of_refines (input : StructuralContext β) (policy : Handler State (Events Φ))
    (exposes : Exposes policy) (a b : Operand Φ (β.snoc A) B)
    (forward : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b))
    (backward : HandledTrace.Program.Refines (model Φ) policy (pack β b) (pack β a)) :
    Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  equiv_of_refines_proof input policy exposes a b forward backward

/-! ## Faithful semantic functors -/

/-- At the free interpretation and a policy that replays every complete
history, the semantic functor is injective on native classes. -/
theorem handledFunctor_map_injective (input : StructuralContext β) (policy : Handler State (Events Φ))
    (exposes : Exposes policy) {X Y : Case.Interface Φ β input} :
    Function.Injective ((handledFunctor (model Φ) policy input).map (X := X) (Y := Y)) := by
  intro p q
  refine Quotient.inductionOn₂ p q fun a b same => Quotient.sound ?_
  have refines := HandledTrace.Arrow.ofProgram_eq_iff.mp same
  exact equiv_of_refines input policy exposes a b refines.1 refines.2

theorem handledFunctor_faithful (input : StructuralContext β) (policy : Handler State (Events Φ))
    (exposes : Exposes policy) : (handledFunctor (model Φ) policy input).Faithful :=
  ⟨fun {_ _} => handledFunctor_map_injective input policy exposes⟩

/-- The same holds for written ranked graphs through the actual emitter. -/
theorem ssaHandledFunctor_faithful (input : StructuralContext β) (policy : Handler State (Events Φ))
    (exposes : Exposes policy) : (ssaHandledFunctor (model Φ) policy input).Faithful :=
  ⟨fun {_ _} p q same => by
    have emitted := handledFunctor_map_injective input policy exposes same
    rw [← readbackFunctor_map_emitFunctor_map input p, emitted, readbackFunctor_map_emitFunctor_map]⟩

/-- Two native classes are equal exactly when the scripted policy gives
them the same handled-trace arrow. -/
theorem scripted_map_eq_iff (input : StructuralContext β) {X Y : Case.Interface Φ β input} (p q : X ⟶ Y) :
    (handledFunctor (model Φ) (scripted Φ) input).map p = (handledFunctor (model Φ) (scripted Φ) input).map q ↔
      p = q :=
  ⟨fun same => handledFunctor_map_injective input (scripted Φ) scripted_exposes same, fun same => by rw [same]⟩

/-- The same statement for the permissive policy. -/
theorem permissive_map_eq_iff (input : StructuralContext β) {X Y : Case.Interface Φ β input} (p q : X ⟶ Y) :
    (handledFunctor (model Φ) (permissive Φ) input).map p =
        (handledFunctor (model Φ) (permissive Φ) input).map q ↔ p = q :=
  ⟨fun same => handledFunctor_map_injective input (permissive Φ) permissive_exposes same, fun same => by rw [same]⟩

end Free

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

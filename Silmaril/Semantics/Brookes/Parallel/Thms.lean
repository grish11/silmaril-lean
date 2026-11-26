module

public import Silmaril.Semantics.Brookes.Parallel.Defs
public import Silmaril.Semantics.Brookes.Thms
import Silmaril.Proofs.Semantics.Brookes.ReturnedParallel

public section

namespace Silmaril.Semantics.Brookes.Behavior

universe u v w x y

variable {Store : Type u} {A : Type v} {B : Type w} {C : Type x} {D : Type y}

/-- Pure result mapping agrees with Kleisli extension by return. -/
theorem mapResult_eq_bind (f : A → B) (p : Behavior Store A) :
    p.mapResult f = p.bind (ret ∘ f) :=
  Proofs.Semantics.Brookes.ReturnedParallel.mapResult_eq_bind f p

/-- Mapping a pure result gives the return of the mapped value. -/
theorem mapResult_ret (f : A → B) (a : A) :
    (ret (Store := Store) a).mapResult f = ret (f a) :=
  Proofs.Semantics.Brookes.ReturnedParallel.mapResult_ret f a

/-- Mapping the final result commutes with applying a continuation. -/
theorem mapResult_bind (f : B → C) (p : Behavior Store A) (k : A → Behavior Store B) :
    (p.bind k).mapResult f = p.bind (fun a => (k a).mapResult f) :=
  Proofs.Semantics.Brookes.ReturnedParallel.mapResult_bind f p k

/-- Mapping before bind precomposes the continuation. -/
theorem bind_mapResult (f : A → B) (p : Behavior Store A) (k : B → Behavior Store C) :
    (p.mapResult f).bind k = p.bind (k ∘ f) :=
  Proofs.Semantics.Brookes.ReturnedParallel.bind_mapResult f p k

/-- Two pure result mappings compose without changing the word. -/
theorem mapResult_comp (f : A → B) (g : B → C) (p : Behavior Store A) :
    (p.mapResult f).mapResult g = p.mapResult (g ∘ f) :=
  Proofs.Semantics.Brookes.ReturnedParallel.mapResult_comp f g p

/-- Membership is witnessed by a shuffle and a closing deduction. -/
theorem parallel_accepts_iff {p : Behavior Store A} {q : Behavior Store B} {trace : Trace Store}
    {a : A} {b : B} :
    (p.parallel q).accepts trace (a, b) ↔
      ∃ left right merged, p.accepts left a ∧ q.accepts right b ∧
        Shuffle left right merged ∧ Reduces merged trace :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_accepts_iff

/-- Closing the inputs before shuffling gives the same behavior as closing the raw shuffle. -/
theorem parallel_generate (leftSeed : Trace Store → A → Prop)
    (rightSeed : Trace Store → B → Prop) :
    (generate leftSeed).parallel (generate rightSeed) =
      generate (fun word result =>
        ∃ left right, left ≠ [] ∧ right ≠ [] ∧ leftSeed left result.1 ∧
          rightSeed right result.2 ∧ Shuffle left right word) :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_generate leftSeed rightSeed

/-- Parallel is natural in both pure result maps. -/
theorem parallel_natural (f : A → C) (g : B → D) (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).mapResult (Prod.map f g) = (p.mapResult f).parallel (q.mapResult g) :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_natural f g p q

/-- Swapping the results exchanges the two operands. -/
theorem parallel_symm (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).mapResult Prod.swap = q.parallel p :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_symm p q

/-- Reassociating the returned tuple reassociates parallel. -/
theorem parallel_assoc (p : Behavior Store A) (q : Behavior Store B) (r : Behavior Store C) :
    ((p.parallel q).parallel r).mapResult (fun ((a, b), c) => (a, b, c)) =
      p.parallel (q.parallel r) :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_assoc p q r

/-- A pure left operand supplies a fixed context. -/
theorem parallel_ret_left (a : A) (q : Behavior Store B) :
    (ret a).parallel q = q.strength a :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_ret_left a q

/-- A pure right operand adds its value to the result. -/
theorem parallel_ret_right (p : Behavior Store A) (b : B) :
    p.parallel (ret b) = p.mapResult (fun a => (a, b)) :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_ret_right p b

/-- Unit return is a left unit under the product unitor. -/
theorem parallel_unit_left (p : Behavior Store A) :
    ((ret ()).parallel p).mapResult Prod.snd = p :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_unit_left p

/-- Unit return is a right unit under the product unitor. -/
theorem parallel_unit_right (p : Behavior Store A) :
    (p.parallel (ret ())).mapResult Prod.fst = p :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_unit_right p

/-- Two pure operands return their pair. -/
theorem parallel_pure (a : A) (b : B) :
    (ret (Store := Store) a).parallel (ret b) = ret (a, b) :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_pure a b

/-- Erasing the return agrees with the core command parallel. -/
theorem forget_parallel (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).forget = Command.parallel p.forget q.forget :=
  Proofs.Semantics.Brookes.ReturnedParallel.forget_parallel p q

/-- Closed sequential observations compose through one intermediate store and value. -/
theorem bind_completes_iff {p : Behavior Store A} {k : A → Behavior Store B} {s t : Store}
    {b : B} :
    (p.bind k).completes s t b ↔
      ∃ m a, p.completes s m a ∧ (k a).completes m t b :=
  Proofs.Semantics.Brookes.ReturnedParallel.bind_completes_iff

/-- Closed parallel observations are witnessed by contiguous runs of finite schedules. -/
theorem parallel_completes_iff {p : Behavior Store A} {q : Behavior Store B} {s t : Store}
    {a : A} {b : B} :
    (p.parallel q).completes s t (a, b) ↔
      ∃ left right merged, p.accepts left a ∧ q.accepts right b ∧
        Shuffle left right merged ∧ Runs s merged t :=
  Proofs.Semantics.Brookes.ReturnedParallel.parallel_completes_iff

/-- Doing the first phase of both threads before either continuation is an admissible schedule. -/
theorem interchange_inclusion {p : Behavior Store A} {q : Behavior Store B}
    {k : A → Behavior Store C} {l : B → Behavior Store D} {trace : Trace Store} {c : C} {d : D}
    (h : ((p.parallel q).bind (fun (a, b) => (k a).parallel (l b))).accepts trace (c, d)) :
    ((p.bind k).parallel (q.bind l)).accepts trace (c, d) :=
  Proofs.Semantics.Brookes.ReturnedParallel.interchange_inclusion h

/-- Two writes and a read witness strict interchange on a closed store observation. -/
theorem shared_store_interchange_strict :
    ∃ (p q : Behavior Nat Unit) (k : Unit → Behavior Nat Nat) (l : Unit → Behavior Nat Unit),
      ((p.bind k).parallel (q.bind l)).completes 0 2 (1, ()) ∧
      ¬((p.parallel q).bind (fun (a, b) => (k a).parallel (l b))).completes 0 2 (1, ()) :=
  Proofs.Semantics.Brookes.ReturnedParallel.shared_store_interchange_strict

end Silmaril.Semantics.Brookes.Behavior

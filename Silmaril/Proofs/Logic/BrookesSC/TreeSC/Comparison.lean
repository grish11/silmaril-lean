module

public import Silmaril.Logic.BrookesSC.TreeSC.Defs
public import Silmaril.Logic.BrookesSC.Concrete.Thms
public import Silmaril.Semantics.Brookes.StoreEquiv.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms

public section

namespace Silmaril.Proofs.Logic.BrookesSC.TreeSC

open CategoryTheory Silmaril.Logic.BrookesSC Silmaril.Semantics.Brookes
open Silmaril.Logic.BrookesSC.TreeSC (accessMode encode inequation signature storeEquiv world)
open Silmaril.Semantics.Brookes.TreeSC (Code readBehavior writeBehavior treeBehavior treeBehavior_code)
open Silmaril.Semantics.TrackA.Interaction (WeakITree)

variable {R X : Type} {S T : Signature (world R)}

theorem encode_translate (labels : signature R ⟶ S) (f : S ⟶ T)
    (code : Code R) : (encode labels code).translate f = encode (labels ≫ f) code := by
  induction code with
  | done => rfl
  | load mode loc next ih => simp only [encode, Program.translate, ih]; rfl
  | store mode loc value next ih => simp only [encode, Program.translate, ih]; rfl
  | acquire lock _ _ | release lock _ _ => exact lock.elim

theorem inequation_translate (labels : signature R ⟶ S) (f : S ⟶ T)
    (lhs rhs : X → Code R) :
    (inequation labels lhs rhs).translate f = inequation (labels ≫ f) lhs rhs := by
  unfold Sentence.translate inequation
  simp only [encode_translate]

variable [DecidableEq R]

private theorem load_transport
    (mode : Silmaril.Semantics.TrackA.Concurrency.AccessMode) (loc : R) :
    (readBehavior loc).transport (storeEquiv R) =
      Concrete.primitive (.load () (accessMode mode) loc) := by
  apply Behavior.ext
  intro word reply
  rw [readBehavior, Behavior.transport_atomic, Behavior.atomic_accepts_iff,
    Concrete.primitive_accepts_iff]
  constructor
  · rintro ⟨s, t, ⟨h, rfl⟩, reduces⟩
    have eq := (storeEquiv R).symm.injective h
    subst t
    exact ⟨s, s, rfl, reduces⟩
  · rintro ⟨s, t, step, reduces⟩
    have eq : s.memory loc = reply ∧ s = t := Prod.mk.inj (Option.some.inj step)
    obtain ⟨rfl, rfl⟩ := eq
    exact ⟨s, s, ⟨rfl, rfl⟩, reduces⟩

private theorem write_transport_accepts
    (mode : Silmaril.Semantics.TrackA.Concurrency.AccessMode) (loc : R) (value : Nat)
    (word : Trace (Concrete.Store (world R))) (reply : PUnit) :
    (Concrete.primitive (.store () (accessMode mode) loc value)).accepts word reply ↔
      ((writeBehavior loc value).transport (storeEquiv R)).accepts word () := by
  cases reply
  rw [Concrete.primitive_accepts_iff, writeBehavior, Behavior.transport_atomic,
    Behavior.atomic_accepts_iff]
  refine exists_congr fun s => exists_congr fun t => and_congr ?_ Iff.rfl
  change some (PUnit.unit, {s with memory := Function.update s.memory loc value}) =
    some (PUnit.unit, t) ↔ t.memory = Function.update s.memory loc value
  constructor
  · intro h
    exact congrArg Concrete.Store.memory (Prod.mk.inj (Option.some.inj h)).2.symm
  · intro h
    have eq : t = {s with memory := Function.update s.memory loc value} :=
      (storeEquiv R).symm.injective h
    subst t
    rfl

private theorem write_bind (mode : Silmaril.Semantics.TrackA.Concurrency.AccessMode)
    (loc : R) (value : Nat) (next : Behavior (Concrete.Store (world R)) Unit) :
    (Concrete.primitive (.store () (accessMode mode) loc value)).bind (fun _ => next) =
      ((writeBehavior loc value).transport (storeEquiv R)).bind (fun _ => next) := by
  apply Behavior.ext
  intro word result
  simp only [Behavior.bind_accepts_iff]
  constructor
  · rintro ⟨left, right, reply, run, rest, reduce⟩
    exact ⟨left, right, (), (write_transport_accepts mode loc value left reply).mp run, rest, reduce⟩
  · rintro ⟨left, right, _, run, rest, reduce⟩
    exact ⟨left, right, ⟨⟩, (write_transport_accepts mode loc value left ⟨⟩).mpr run, rest, reduce⟩

theorem eval_encode_denote (labels : signature R ⟶ S)
    (M : Concrete.TraceModel S) (code : Code R) :
    M.eval (encode labels code) = code.denote.transport (storeEquiv R) := by
  induction code with
  | done => rw [encode, Concrete.eval_ret, Code.denote, Behavior.transport_ret]
  | load mode loc next ih =>
    rw [encode, Concrete.eval_call_primitive, Code.denote, Behavior.transport_bind, load_transport mode]
    simp only [ih]
  | store mode loc value next ih =>
    rw [encode, Concrete.eval_call_primitive, Code.denote, Behavior.transport_bind, write_bind, ih]
  | acquire lock _ _ | release lock _ _ => exact lock.elim

theorem satisfies_iff (labels : signature R ⟶ S)
    (M : Concrete.TraceModel S) (lhs rhs : X → Code R) :
    (inequation labels lhs rhs).Satisfies M ↔
      ∀ (x : X) (word : Trace (Silmaril.Semantics.Brookes.TreeSC.Store R)),
        (treeBehavior WeakITree.unfold (lhs x).toTree).accepts word () →
        (treeBehavior WeakITree.unfold (rhs x).toTree).accepts word () := by
  simp only [Concrete.satisfies_iff, inequation, treeBehavior_code, eval_encode_denote]
  constructor
  · intro h x word run
    have accepts := Behavior.transport_accepts_iff (storeEquiv R) (lhs x).denote
      (Trace.mapStores (storeEquiv R) word) ()
    have accepts' := Behavior.transport_accepts_iff (storeEquiv R) (rhs x).denote
      (Trace.mapStores (storeEquiv R) word) ()
    rw [Trace.mapStores_inverse] at accepts accepts'
    exact accepts'.mp (h x (accepts.mpr run))
  · intro h x word value run
    cases value
    exact (Behavior.transport_accepts_iff _ _ _ _).mpr
      (h x _ ((Behavior.transport_accepts_iff _ _ _ _).mp run))

end Silmaril.Proofs.Logic.BrookesSC.TreeSC

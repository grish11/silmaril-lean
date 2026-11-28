module

public import Silmaril.Semantics.ITree.Trace.Thms
public import Mathlib.Logic.Equiv.Sum

/-! # Typed request, tree and handler trace transport -/

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v w

variable {E F : Type u → Type u} {A B : Type v}

/-- The reply type paired with a request of that type. -/
abbrev Request (E : Type u → Type u) := (R : Type u) × E R

/-- A bijection of packed requests with a separate reply bijection at each
request. Continuations use the inverse reply map. -/
structure SignatureEquiv (E F : Type u → Type u) where
  request : Request E ≃ Request F
  reply (q : Request E) : q.1 ≃ (request q).1

namespace SignatureEquiv

def refl (E : Type u → Type u) : SignatureEquiv E E where
  request := Equiv.refl _
  reply q := Equiv.refl q.1

def trans {G : Type u → Type u} (e : SignatureEquiv E F) (f : SignatureEquiv F G) :
    SignatureEquiv E G where
  request := e.request.trans f.request
  reply q := (e.reply q).trans (f.reply (e.request q))

def visibleEquiv {X Y : Type w} (e : SignatureEquiv E F) (a : A ≃ B) (x : X ≃ Y) :
    Visible E A X ≃ Visible F B Y :=
  let pack := fun (G : Type u → Type u) (C : Type v) (Z : Type w) =>
    (⟨fun
        | .ret c => .inl c
        | .vis ev k => .inr ⟨⟨_, ev⟩, k⟩,
      fun
        | .inl c => .ret c
        | .inr ⟨⟨_, ev⟩, k⟩ => .vis ev k,
      fun z => by cases z <;> rfl,
      fun z => by rcases z with c | ⟨⟨R, ev⟩, k⟩ <;> rfl⟩ :
      Visible G C Z ≃ C ⊕ ((q : Request G) × (q.1 → Z)))
  (pack E A X).trans
    ((Equiv.sumCongr a (Equiv.sigmaCongr e.request fun q => Equiv.arrowCongr (e.reply q) x)).trans
      (pack F B Y).symm)

def trace (e : SignatureEquiv E F) (a : A ≃ B) : ITree.Trace E A → ITree.Trace F B
  | .prefix => .prefix
  | .request ev => .request (e.request ⟨_, ev⟩).2
  | .exchange ev r tail =>
      .exchange (e.request ⟨_, ev⟩).2 (e.reply ⟨_, ev⟩ r) (trace e a tail)
  | .result b => .result (a b)

def approx (e : SignatureEquiv E F) (a : A ≃ B) :
    (n : Nat) → Approx E A n ≃ Approx F B n
  | 0 => Equiv.refl _
  | n + 1 =>
    let v := e.visibleEquiv a (e.approx a n)
    ⟨Part.map v, Part.map v.symm,
      fun x => by simp [Part.map_map, Part.map_id', Function.comp_def],
      fun x => by simp [Part.map_map, Part.map_id', Function.comp_def]⟩

theorem approx_truncate (e : SignatureEquiv E F) (a : A ≃ B)
    (n : Nat) (x : Approx E A (n + 1)) :
    Approx.truncate n (e.approx a (n + 1) x) = e.approx a n (Approx.truncate n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [approx, Equiv.coe_fn_mk, Approx.truncate, Part.map_eq_map, Part.map_map]
    congr 1
    funext node
    cases node with
    | ret value => rfl
    | @vis R ev k =>
      let inv := (e.reply ⟨R, ev⟩).symm
      change Visible.vis _ (fun r => Approx.truncate n (e.approx a (n + 1) (k (inv r)))) =
        Visible.vis _ (fun r => e.approx a n (Approx.truncate n (k (inv r))))
      congr 1
      funext r
      exact ih _

/-- Rename every finite observation coherently in the existing weak tree.
The tree's finite silent step is the identity. -/
def tree (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A) : Tree F B where
  observe n := e.approx a n (t.observe n)
  coherent n := by rw [e.approx_truncate, t.coherent]

/-- Transport is invertible at the level of coherent finite observations. -/
def treeEquiv (e : SignatureEquiv E F) (a : A ≃ B) : Tree E A ≃ Tree F B where
  toFun := e.tree a
  invFun t := {
    observe n := (e.approx a n).symm (t.observe n)
    coherent n := by
      apply (e.approx a n).injective
      rw [← e.approx_truncate, Equiv.apply_symm_apply, Equiv.apply_symm_apply, t.coherent] }
  left_inv t := Tree.ext fun n => (e.approx a n).symm_apply_apply _
  right_inv t := Tree.ext fun n => (e.approx a n).apply_symm_apply _

end SignatureEquiv

/-- A handler admits a visible exchange when the request and its actual typed
reply can take the current state to the successor state. -/
abbrev Handler (S : Type w) (E : Type u → Type u) :=
  (q : Request E) → S → q.1 → S → Prop

/-- A finite replay checks completed exchanges. A pending request can still
be observed when the handler offers no legal reply. -/
def Replay {S : Type w} (step : Handler S E) (s : S) : Trace E A → Prop
  | .exchange ev r tail => ∃ s', step ⟨_, ev⟩ s r s' ∧ Replay step s' tail
  | _ => True

/-- Finite observations of an actual weak ITree admitted by the handler. -/
def HandledTrace {S : Type w} (step : Handler S E) (s : S) (t : Tree E A)
    (p : Trace E A) : Prop :=
  HasTrace t p ∧ Replay step s p

end Silmaril.Elgot.ITree

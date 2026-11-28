module

public import Silmaril.Semantics.ITree.Reindex.Defs
import Silmaril.Proofs.Semantics.ITree.Reindex.Transport
import Silmaril.Proofs.Semantics.ITree.Reindex.Evaluation

public section

namespace Silmaril.Elgot.ITree

universe u v w w'

variable {E F : Type u → Type u} {A B : Type v}
  {S : Type w} {T : Type w'} {step : Handler S E} {step' : Handler T F}

@[simp] theorem SignatureEquiv.tree_refl (t : Tree E A) :
    (SignatureEquiv.refl E).tree (Equiv.refl A) t = t :=
  Silmaril.Proofs.ITree.Reindex.tree_refl t

theorem SignatureEquiv.tree_trans {G : Type u → Type u} {C : Type v}
    (e : SignatureEquiv E F) (f : SignatureEquiv F G) (a : A ≃ B) (b : B ≃ C)
    (t : Tree E A) :
    (e.trans f).tree (a.trans b) t = f.tree b (e.tree a t) :=
  Silmaril.Proofs.ITree.Reindex.tree_trans e f a b t

theorem SignatureEquiv.out_tree (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A) :
    out (e.tree a t) = Part.map (e.visibleEquiv a (e.treeEquiv a)) (out t) :=
  Silmaril.Proofs.ITree.Reindex.out_tree e a t

@[simp] theorem SignatureEquiv.tree_ret (e : SignatureEquiv E F) (a : A ≃ B) (b : A) :
    e.tree a (ret b) = ret (a b) := by
  apply out_injective
  simp only [e.out_tree, out_ret, Part.map_some]
  rfl

@[simp] theorem SignatureEquiv.tree_vis (e : SignatureEquiv E F) (a : A ≃ B)
    {R : Type u} (ev : E R) (k : R → Tree E A) :
    e.tree a (vis ev k) = vis (e.request ⟨R, ev⟩).2
      (fun r => e.tree a (k ((e.reply ⟨R, ev⟩).symm r))) := by
  apply out_injective
  simp only [e.out_tree, out_vis, Part.map_some]
  rfl

@[simp] theorem SignatureEquiv.tree_tau (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A) :
    e.tree a (tau t) = tau (e.tree a t) := rfl

/-- Reindexing commutes with sequencing when the continuations agree at
corresponding input values. -/
theorem SignatureEquiv.tree_bind {A' B' : Type v} (e : SignatureEquiv E F)
    (a : A ≃ A') (b : B ≃ B') (t : Tree E A)
    (k : A → Tree E B) (l : A' → Tree F B') (h : ∀ z, e.tree b (k z) = l (a z)) :
    e.tree b (t >>= k) = (e.tree a t >>= l) :=
  Silmaril.Proofs.ITree.Reindex.tree_bind e a b t k l h

/-- Reindex both the loop state and the exit value. This holds for arbitrary
weak-tree bodies, including silent feedback and divergence. -/
theorem SignatureEquiv.tree_iter {A' B' : Type v} (e : SignatureEquiv E F)
    (a : A ≃ A') (b : B ≃ B') (f : A → Tree E (B ⊕ A)) (g : A' → Tree F (B' ⊕ A'))
    (h : ∀ z, e.tree (Equiv.sumCongr b a) (f z) = g (a z)) (x : A) :
    e.tree b (Elgot.iter f x) = Elgot.iter g (a x) :=
  Silmaril.Proofs.ITree.Reindex.tree_iter e a b f g h x

theorem SignatureEquiv.trace_surjective (e : SignatureEquiv E F) (a : A ≃ B) :
    Function.Surjective (e.trace a) :=
  Silmaril.Proofs.ITree.Reindex.trace_surjective e a

theorem SignatureEquiv.hasTrace_iff (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A)
    (p : Trace E A) : HasTrace (e.tree a t) (e.trace a p) ↔ HasTrace t p :=
  Silmaril.Proofs.ITree.Reindex.hasTrace_tree_iff e a t p

/-- A two-way step law lifts through every finite sequence of completed
exchanges. Prefix, pending request and return endpoints require no step. -/
theorem SignatureEquiv.replay_iff (e : SignatureEquiv E F) (a : A ≃ B) (s : S ≃ T)
    (hstep : ∀ q x r y, step' (e.request q) (s x) (e.reply q r) (s y) ↔ step q x r y)
    (x : S) (p : Trace E A) :
    Replay step' (s x) (e.trace a p) ↔ Replay step x p :=
  Silmaril.Proofs.ITree.Reindex.replay_iff e a s hstep x p

theorem SignatureEquiv.handledTrace_iff (e : SignatureEquiv E F) (a : A ≃ B) (s : S ≃ T)
    (hstep : ∀ q x r y, step' (e.request q) (s x) (e.reply q r) (s y) ↔ step q x r y)
    (x : S) (t : Tree E A) (p : Trace E A) :
    HandledTrace step' (s x) (e.tree a t) (e.trace a p) ↔ HandledTrace step x t p :=
  and_congr (e.hasTrace_iff a t p) (e.replay_iff a s hstep x p)

/-- The unrestricted one-state handler replays every finite trace. -/
theorem Replay.allReplies (p : Trace E A) : Replay (fun _ (_ : Unit) _ (_ : Unit) => True) () p := by
  induction p with
  | «prefix» | request | result => trivial
  | exchange _ _ _ ih => exact ⟨(), trivial, ih⟩

/-- At the same initial state and under the same handler, the target can
reuse the source replay of the exact trace. -/
theorem TraceLE.handledTrace {source target : Tree E A} (included : TraceLE source target)
    {x : S} {p : Trace E A} (seen : HandledTrace step x source p) :
    HandledTrace step x target p :=
  ⟨included p seen.1, seen.2⟩

/-- The target language is the image under trace renaming. -/
theorem SignatureEquiv.handledTrace_image (e : SignatureEquiv E F) (a : A ≃ B) (s : S ≃ T)
    (hstep : ∀ q x r y, step' (e.request q) (s x) (e.reply q r) (s y) ↔ step q x r y)
    (x : S) (t : Tree E A) (p' : Trace F B) :
    HandledTrace step' (s x) (e.tree a t) p' ↔
      ∃ p, HandledTrace step x t p ∧ e.trace a p = p' := by
  obtain ⟨p, rfl⟩ := e.trace_surjective a p'
  exact ⟨fun h => ⟨p, (e.handledTrace_iff a s hstep x t p).mp h, rfl⟩,
    fun ⟨q, h, eq⟩ => eq ▸ (e.handledTrace_iff a s hstep x t q).mpr h⟩

end Silmaril.Elgot.ITree

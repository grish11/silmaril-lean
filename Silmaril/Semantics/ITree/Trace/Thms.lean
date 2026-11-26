module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Semantics.ITree.Trace

/-! # Weak trace inclusion and sequential composition -/

public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

@[refl] theorem TraceLE.refl (t : Tree E A) : TraceLE t t :=
  fun _ h => h

theorem TraceLE.trans {t s r : Tree E A} (h : TraceLE t s) (g : TraceLE s r) :
    TraceLE t r :=
  fun p hp => g p (h p hp)

/-- For deterministic weak trees, mutual inclusion fixes the root and every
typed reply continuation, hence every finite approximation. -/
theorem TraceLE.antisymm {t s : Tree E A} (hts : TraceLE t s) (hst : TraceLE s t) :
    t = s :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_antisymm hts hst

theorem eq_iff_traceLE {t s : Tree E A} : t = s ↔ TraceLE t s ∧ TraceLE s t :=
  ⟨fun h => h ▸ ⟨TraceLE.refl t, TraceLE.refl t⟩, fun h => h.1.antisymm h.2⟩

/-- The trace order on weak trees. Equality on `Tree` already identifies
weakly equal representatives. Use this order explicitly or as a local
instance. -/
@[expose, instance_reducible] def Tree.tracePartialOrder : PartialOrder (Tree E A) where
  le := TraceLE
  le_refl := TraceLE.refl
  le_trans _ _ _ := TraceLE.trans
  le_antisymm _ _ := TraceLE.antisymm

-- Weak tree equality is equality in this model, and tau is the identity.
@[simp] theorem traceLE_tau_left (t s : Tree E A) : TraceLE (tau t) s ↔ TraceLE t s := Iff.rfl

@[simp] theorem traceLE_tau_right (t s : Tree E A) : TraceLE t (tau s) ↔ TraceLE t s := Iff.rfl

@[simp] theorem hasTrace_diverge_iff (p : Trace E A) :
    HasTrace (diverge : Tree E A) p ↔ p = .prefix :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_diverge_iff p

theorem traceLE_diverge (t : Tree E A) : TraceLE diverge t := by
  intro p hp
  rw [(hasTrace_diverge_iff p).mp hp]
  trivial

theorem hasTrace_vis_request {R : Type u} (e : E R) (k : R → Tree E A) :
    HasTrace (vis e k) (.request e) :=
  ⟨k, out_vis e k⟩

theorem hasTrace_vis_request_iff {R S : Type u} (e : E R) (k : R → Tree E A) (d : E S) :
    HasTrace (vis e k) (.request d) ↔ ∃ h : S = R, h ▸ d = e :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_request_vis_iff e k d

theorem hasTrace_vis_exchange {R S : Type u} (e : E R) (k : R → Tree E A)
    (d : E S) (r : S) (p : Trace E A) :
    HasTrace (vis e k) (.exchange d r p) ↔
      ∃ h : S = R, h ▸ d = e ∧ HasTrace (k (h ▸ r)) p :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_exchange_vis_iff e k d r p

@[simp] theorem hasTrace_vis_exchange_iff {R : Type u} (e : E R) (k : R → Tree E A)
    (r : R) (p : Trace E A) :
    HasTrace (vis e k) (.exchange e r p) ↔ HasTrace (k r) p :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_same_exchange_iff e k r p

theorem TraceLE.vis {R : Type u} (e : E R) {k l : R → Tree E A}
    (h : ∀ r, TraceLE (k r) (l r)) : TraceLE (vis e k) (vis e l) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_vis_mono e h

/-- A common producer preserves inclusion of the continuations at each
returned value. The proof follows the same typed reply through any producer
request before recurring on the rest of the finite trace. -/
theorem TraceLE.bind_right (t : Tree E A) {f g : A → Tree E B}
    (h : ∀ a, TraceLE (f a) (g a)) : TraceLE (t >>= f) (t >>= g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_bind_right_mono t h

/-- A common continuation preserves inclusion of the producers. Each
terminating observation supplies the same value to that continuation. -/
theorem TraceLE.bind_left {t s : Tree E A} (h : TraceLE t s) (f : A → Tree E B) :
    TraceLE (t >>= f) (s >>= f) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_bind_left_mono h f

/-- Monotonicity in both the producer and the returned-value continuation. -/
theorem TraceLE.bind {t s : Tree E A} {f g : A → Tree E B}
    (h : TraceLE t s) (hfg : ∀ a, TraceLE (f a) (g a)) :
    TraceLE (t >>= f) (s >>= g) :=
  (h.bind_left f).trans (TraceLE.bind_right s hfg)

/-- A pure return map takes the image of the observations under `Trace.map`.
In particular it introduces no request, and it can merge result observations. -/
theorem hasTrace_bind_pure_iff (f : A → B) (t : Tree E A) (p : Trace E B) :
    HasTrace (t >>= fun a => pure (f a)) p ↔ ∃ q, HasTrace t q ∧ q.map f = p :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_map_iff f t p

/-- An injective return tag preserves and reflects the particular mapped trace. -/
theorem hasTrace_bind_pure_map_iff {f : A → B} (injective : Function.Injective f) (tree : Tree E A)
    (trace : Trace E A) :
    HasTrace (tree >>= fun x => pure (f x)) (trace.map f) ↔ HasTrace tree trace :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_bind_pure_map_iff injective tree trace

theorem TraceLE.bind_pure {t s : Tree E A} (h : TraceLE t s) (f : A → B) :
    TraceLE (t >>= fun a => pure (f a)) (s >>= fun a => pure (f a)) :=
  h.bind_left (fun a => pure (f a))

/-- An injective pure result encoding reflects the trace order. All requests
and actual typed replies remain in the original event signature. -/
theorem TraceLE.bind_pure_iff {t s : Tree E A} {f : A → B} (hf : Function.Injective f) :
    TraceLE (t >>= fun a => pure (f a)) (s >>= fun a => pure (f a)) ↔ TraceLE t s :=
  ⟨Silmaril.Proofs.Semantics.Elgot.ITree.trace_bind_pure_reflect hf, fun h => h.bind_pure f⟩

/-- A visible root of a resumed computation is witnessed by a finite run
of the normalizer. Each recursive return goes to another body. The final
step exposes a return or an indexed request with resumed continuations. -/
theorem out_resume_runs_iff (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A))
    (node : Visible E B (Tree E B)) :
    out (resume f t) = Part.some node ↔ Elgot.Part.Runs (normalizeStep f) t node :=
  Silmaril.Proofs.Semantics.Elgot.ITree.out_resume_runs_iff f t node

/-- Resumption preserves refinement of the current body and pointwise
refinement of the bodies reached by recursive returns. -/
theorem TraceLE.resume {f g : A → Tree E (B ⊕ A)} {t s : Tree E (B ⊕ A)}
    (hfg : ∀ a, TraceLE (f a) (g a)) (hts : TraceLE t s) :
    TraceLE (resume f t) (resume g s) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_resume_mono hfg hts

/-- The weak Elgot iterator is monotone in its body for finite traces. -/
theorem TraceLE.iter {f g : A → Tree E (B ⊕ A)}
    (hfg : ∀ a, TraceLE (f a) (g a)) (a : A) :
    TraceLE (Elgot.iter f a) (Elgot.iter g a) := by
  simpa only [resume_body] using TraceLE.resume hfg (hfg a)

end Silmaril.Elgot.ITree

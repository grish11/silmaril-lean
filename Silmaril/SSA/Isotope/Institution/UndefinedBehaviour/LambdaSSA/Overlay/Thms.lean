module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Composition
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Conservativity
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeSubstitution

/-! # Conservativity and directed label substitution for explicit region UB -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational

universe u v w x

namespace Behaviour

variable {n m : Nat} {α : Type w} {σ : Type x}

theorem bind_mono {p q : Behaviour n α σ} {k h : Fin n → Value α → σ → Behaviour m α σ}
    (pq : p ≤ q) (kh : ∀ i a s, k i a s ≤ h i a s) : p.bind k ≤ q.bind h :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.bind_mono pq kh

@[simp] theorem top_bind (k : Fin n → Value α → σ → Behaviour m α σ) :
    bind (⊤ : Behaviour n α σ) k = ⊤ := by
  classical
  simp [bind]

/-- A reached UB continuation makes the whole substitution UB at the source state. -/
theorem bind_eq_top_of_reaches_top {p : Behaviour n α σ}
    {k : Fin n → Value α → σ → Behaviour m α σ} {i : Fin n} {a : Value α} {s : σ}
    (reached : Outcome.ret i a s ∈ p.possible) (top : k i a s = ⊤) : p.bind k = ⊤ := by
  classical
  exact ite_eq_left (Or.inr ⟨i, a, s, reached, top⟩)

@[simp] theorem coe_bind (p : Set (Outcome n α σ)) (k : Fin n → Value α → σ → Set (Outcome m α σ)) :
    bind (m := m) (↑p : Behaviour n α σ) (fun i a s => ↑(k i a s)) = ↑(Outcome.bind p k) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.coe_bind p k

end Behaviour

/-- Plain universal outcome sets fail left absorption for ordinary label
sequencing across interfaces. An empty source interface cannot produce a
return at an available target label. -/
theorem bind_empty_ne_univ {m : Nat} {α : Type w} {σ : Type x} {i : Fin m}
    (a : Value α) (s : σ) (k : Fin 0 → Value α → σ → Set (Outcome m α σ)) :
    Outcome.bind Set.univ k ≠ Set.univ :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.bind_empty_ne_univ (i := i) a s k

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {Γ L K : VCtx τ}

/-- The ordinary observation projection recovers every native observation. -/
@[simp] theorem observe_native (r : UB.Typed (Φ := Φ) Γ L) (M : Model.{u,w,x} Φ Γ.length) :
    observe (.native r) M = UB.observe M r :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.observe_native r M

/-- At a fixed model, native observational inclusion is precisely the
pointwise lifted order. This bridge uses the native embedding, whose
denotations are ordinary outcome sets. -/
theorem native_observe_subset_iff (M : Model.{u,w,x} Φ Γ.length)
    (r t : UB.Typed (Φ := Φ) Γ L) :
    UB.observe M r ⊆ UB.observe M t ↔ ∀ s, denote (.native r) M s ≤ denote (.native t) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.native_observe_subset_iff M r t

/-- The embedding preserves and reflects the existing native refinement order. -/
theorem native_refines_iff (r t : UB.Typed (Φ := Φ) Γ L) :
    Refines.{u,v,w,x} (.native r) (.native t) ↔ UB.Refines.{u,v,w,x} r t :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.native_refines_iff r t

/-- The native observation view can use any environment agreeing with the
model's captured variables. -/
theorem mem_nativeOutcomes_iff (r : UB.Typed (Φ := Φ) Γ L)
    {M : Model.{u,w,x} Φ Γ.length} {env : Semantics.Env M.α}
    (agree : Morphism.CaseSSA.EnvAgrees env M.bound) (s : M.σ) (o : Outcome L.length M.α M.σ) :
    o ∈ nativeOutcomes r M s ↔
      match o with
      | .ret i a s' => Semantics.Region.Eval M.instr env r.val s i a s'
      | .fault s' => Semantics.Region.Fault M.instr M.faults env r.val s s'
      | .diverge => Semantics.External.Diverges M.instr M.prim (.region env r.val s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.mem_nativeOutcomes r agree s o

theorem nativeLsubst_hasType (r : UB.Typed (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → UB.Typed (Φ := Φ) (L.get i :: Γ) K) :
    (nativeLsubst r k).HasType Γ K :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.nativeLsubst_hasType r k

/-- An all-native substitution agrees with a typed CFG that dispatches each
successful exit to its continuation, including faults and divergence. -/
theorem denote_native_lsubst (r : UB.Typed (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → UB.Typed (Φ := Φ) (L.get i :: Γ) K)
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    denote (.lsubst (.native r) (fun i => .native (k i))) M s =
      denote (.native ⟨nativeLsubst r k, nativeLsubst_hasType r k⟩) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.denote_native_lsubst r k M s

/-- The UB constructor is greatest at every exact interface. -/
theorem refines_ub (r : Region Φ Γ L) : Refines.{u,v,w,x} r .ub :=
  fun _ _ => le_top

/-- Label substitution is directed in both the source and all continuations. -/
theorem lsubst_mono {r t : Region Φ Γ L} {k h : (i : Fin L.length) → Region Φ (L.get i :: Γ) K}
    (rt : Refines.{u,v,w,x} r t) (kh : ∀ i, Refines.{u,v,w,x} (k i) (h i)) :
    Refines.{u,v,w,x} (.lsubst r k) (.lsubst t h) :=
  fun M s => Behaviour.bind_mono (rt M s) (fun i a mid => kh i (extendModel M a) mid)

/-- Substituting into UB preserves UB at the new label interface. -/
@[simp] theorem denote_ub_lsubst (k : (i : Fin L.length) → Region Φ (L.get i :: Γ) K)
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    denote (.lsubst .ub k) M s = ⊤ :=
  Behaviour.top_bind _

end Silmaril.Isotope.LambdaSSA.UB.Overlay

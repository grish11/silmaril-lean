module

public import Silmaril.Semantics.ThreadTrace.Defs
import Silmaril.Proofs.Semantics.ThreadTrace.Monads
import Silmaril.Proofs.Semantics.ThreadTrace.Quotient
import Silmaril.Proofs.Semantics.ThreadTrace.Renaming
import Silmaril.Proofs.Semantics.ThreadTrace.Used

/-! # Thread trace laws

The reader, writer, powerset, and state transformer instances provide the four
named models' `LawfulMonad` instances. The inclusions below preserve `pure` and
`bind`, as does changing output monoids. Use `readThe` for reader inputs,
`get` for the allocative state, and `tell` to emit output.

The allocative carrier admits unrestricted state transitions. For clients that
track name support, `Alloc.RespectsUsed` supplies a compositional invariant at
valid inputs. A continuation may rely on both the unchanged current thread and
the preceding result's support being in its input used set.

`Complete` is a lawful monad of saturated raw computations. Its sequencing
saturates after raw sequencing. With a surjective output homomorphism, projection
and the lift of all representatives give inverse maps. Renaming is defined on
named branches. The alpha quotient describes observations at a fixed input.
-/

public section

namespace Silmaril.ThreadTrace

universe u

variable {T W V A B : Type u}

theorem Nondet.ext {x y : Nondet T W A} (h : ∀ t, x.run t = y.run t) : x = y :=
  Proofs.Semantics.ThreadTrace.nondetExt h

theorem Alloc.ext {x y : Alloc T W A} (h : ∀ t used, x.run t used = y.run t used) : x = y :=
  Proofs.Semantics.ThreadTrace.allocExt h

theorem singleton_injective : Function.Injective (singleton (T := T) (W := W) (A := A)) :=
  Proofs.Semantics.ThreadTrace.singletonInjective

theorem ignoreUsed_injective : Function.Injective (ignoreUsed (T := T) (W := W) (A := A)) :=
  Proofs.Semantics.ThreadTrace.ignoreUsedInjective

theorem readOnly_injective : Function.Injective (readOnly (T := T) (W := W) (A := A)) :=
  Proofs.Semantics.ThreadTrace.readOnlyInjective

theorem mem_readOnly (x : ReadOnly T W A) (t : T) (used final : Set T) (a : A) (w : W) :
    ((a, final), w) ∈ (readOnly x).run t used ↔ final = used ∧ (a, w) ∈ x.run t used :=
  Proofs.Semantics.ThreadTrace.memReadOnly x t used final a w

theorem mem_range_readOnly (x : Alloc T W A) : x ∈ Set.range readOnly ↔
    ∀ t used a final w, ((a, final), w) ∈ x.run t used → final = used :=
  Proofs.Semantics.ThreadTrace.readOnlyRange x

section Monads

variable [Monoid W]

theorem Nondet.mem_bind (x : Nondet T W A) (k : A → Nondet T W B) (t : T) (b : B) (w : W) :
    (b, w) ∈ (x >>= k).run t ↔
      ∃ a w₁ w₂, (a, w₁) ∈ x.run t ∧ (b, w₂) ∈ (k a).run t ∧ w₁ * w₂ = w :=
  Proofs.Semantics.ThreadTrace.memNondetBind x k t b w

theorem Alloc.mem_bind (x : Alloc T W A) (k : A → Alloc T W B) (t : T)
    (used final : Set T) (b : B) (w : W) :
    ((b, final), w) ∈ (x >>= k).run t used ↔
      ∃ a middle w₁ w₂, ((a, middle), w₁) ∈ x.run t used ∧
        ((b, final), w₂) ∈ (k a).run t middle ∧ w₁ * w₂ = w :=
  Proofs.Semantics.ThreadTrace.memAllocBind x k t used final b w

theorem singleton_bind (x : Det T W A) (k : A → Det T W B) :
    singleton (x >>= k) = singleton x >>= fun a => singleton (k a) :=
  Proofs.Semantics.ThreadTrace.singletonBind x k

theorem readOnly_bind (x : ReadOnly T W A) (k : A → ReadOnly T W B) :
    readOnly (x >>= k) = readOnly x >>= fun a => readOnly (k a) :=
  Proofs.Semantics.ThreadTrace.readOnlyBind x k

theorem singleton_pure (a : A) : singleton (pure a : Det T W A) = pure a := rfl

theorem ignoreUsed_pure (a : A) : ignoreUsed (pure a : Nondet T W A) = pure a := rfl

theorem readOnly_pure (a : A) : readOnly (pure a : ReadOnly T W A) = pure a := by
  apply Alloc.ext
  intro t used
  exact Set.image_singleton

theorem ignoreUsed_bind (x : Nondet T W A) (k : A → Nondet T W B) :
    ignoreUsed (x >>= k) = ignoreUsed x >>= fun a => ignoreUsed (k a) := rfl

theorem singleton_map (f : A → B) (x : Det T W A) : singleton (f <$> x) = f <$> singleton x := by
  simp only [← bind_pure_comp, singleton_bind, singleton_pure]

theorem ignoreUsed_map (f : A → B) (x : Nondet T W A) : ignoreUsed (f <$> x) = f <$> ignoreUsed x := by
  simp only [← bind_pure_comp, ignoreUsed_bind, ignoreUsed_pure]

theorem readOnly_map (f : A → B) (x : ReadOnly T W A) : readOnly (f <$> x) = f <$> readOnly x := by
  simp only [← bind_pure_comp, readOnly_bind, readOnly_pure]

variable [Monoid V] (q : W →* V)

theorem Det.mapOutput_bind (x : Det T W A) (k : A → Det T W B) :
    Det.mapOutput q (x >>= k) = Det.mapOutput q x >>= fun a => Det.mapOutput q (k a) :=
  Proofs.Semantics.ThreadTrace.detMapBind q x k

theorem Nondet.mapOutput_bind (x : Nondet T W A) (k : A → Nondet T W B) :
    Nondet.mapOutput q (x >>= k) = Nondet.mapOutput q x >>= fun a => Nondet.mapOutput q (k a) :=
  Proofs.Semantics.ThreadTrace.nondetMapBind q x k

theorem Alloc.mapOutput_bind (x : Alloc T W A) (k : A → Alloc T W B) :
    Alloc.mapOutput q (x >>= k) = Alloc.mapOutput q x >>= fun a => Alloc.mapOutput q (k a) :=
  Proofs.Semantics.ThreadTrace.allocMapBind q x k

theorem Nondet.mem_mapOutput (x : Nondet T W A) (t : T) (a : A) (v : V) :
    (a, v) ∈ (Nondet.mapOutput q x).run t ↔ ∃ w, (a, w) ∈ x.run t ∧ q w = v :=
  Proofs.Semantics.ThreadTrace.memNondetMapOutput q x t a v

theorem Alloc.mem_mapOutput (x : Alloc T W A) (t : T) (used final : Set T) (a : A) (v : V) :
    ((a, final), v) ∈ (Alloc.mapOutput q x).run t used ↔
      ∃ w, ((a, final), w) ∈ x.run t used ∧ q w = v :=
  Proofs.Semantics.ThreadTrace.memMapOutput q x t used final a v

theorem Alloc.mapOutput_pure (a : A) : Alloc.mapOutput q (pure a : Alloc T W A) = pure a :=
  Proofs.Semantics.ThreadTrace.allocMapPure q a

theorem mapOutput_readOnly (x : ReadOnly T W A) :
    Alloc.mapOutput q (readOnly x) = readOnly (ReadOnly.mapOutput q x) :=
  Proofs.Semantics.ThreadTrace.mapReadOnly q x

theorem Det.mapOutput_pure (a : A) : Det.mapOutput q (pure a : Det T W A) = pure a := by
  funext t
  change (a, q 1) = (a, 1)
  rw [map_one]

theorem Nondet.mapOutput_pure (a : A) : Nondet.mapOutput q (pure a : Nondet T W A) = pure a := by
  apply Nondet.ext
  intro t
  change (fun z : A × W => (z.1, q z.2)) '' {(a, 1)} = {(a, 1)}
  simp

theorem ReadOnly.mapOutput_pure (a : A) : ReadOnly.mapOutput q (pure a : ReadOnly T W A) = pure a :=
  funext fun _ => Nondet.mapOutput_pure q a

theorem ReadOnly.mapOutput_bind (x : ReadOnly T W A) (k : A → ReadOnly T W B) :
    ReadOnly.mapOutput q (x >>= k) = ReadOnly.mapOutput q x >>= fun a => ReadOnly.mapOutput q (k a) :=
  funext fun t => Nondet.mapOutput_bind q (x t) (fun a => k a t)

theorem Det.mapOutput_map (f : A → B) (x : Det T W A) :
    Det.mapOutput q (f <$> x) = f <$> Det.mapOutput q x := by
  simp only [← bind_pure_comp, Det.mapOutput_bind, Det.mapOutput_pure]

theorem Nondet.mapOutput_map (f : A → B) (x : Nondet T W A) :
    Nondet.mapOutput q (f <$> x) = f <$> Nondet.mapOutput q x := by
  simp only [← bind_pure_comp, Nondet.mapOutput_bind, Nondet.mapOutput_pure]

theorem ReadOnly.mapOutput_map (f : A → B) (x : ReadOnly T W A) :
    ReadOnly.mapOutput q (f <$> x) = f <$> ReadOnly.mapOutput q x := by
  simp only [← bind_pure_comp, ReadOnly.mapOutput_bind, ReadOnly.mapOutput_pure]

theorem Alloc.mapOutput_map (f : A → B) (x : Alloc T W A) :
    Alloc.mapOutput q (f <$> x) = f <$> Alloc.mapOutput q x := by
  simp only [← bind_pure_comp, Alloc.mapOutput_bind, Alloc.mapOutput_pure]

theorem mapOutput_singleton (x : Det T W A) :
    Nondet.mapOutput q (singleton x) = singleton (Det.mapOutput q x) := by
  apply Nondet.ext
  intro t
  exact Set.image_singleton

theorem mapOutput_ignoreUsed (x : Nondet T W A) :
    ReadOnly.mapOutput q (ignoreUsed x) = ignoreUsed (Nondet.mapOutput q x) := rfl

end Monads

section Used

variable [Monoid W]

theorem mem_fresh (t : T) (used final : Set T) (a : T) (w : W) :
    ((a, final), w) ∈ (fresh (W := W)).run t used ↔
      t ∈ used ∧ a ∉ used ∧ final = insert a used ∧ w = 1 :=
  Proofs.Semantics.ThreadTrace.memFresh t used final a w

theorem fresh_nonempty (t : T) (used : Set T) :
    ((fresh (W := W)).run t used).Nonempty ↔ t ∈ used ∧ ∃ a, a ∉ used :=
  Proofs.Semantics.ThreadTrace.freshNonempty t used

theorem pure_respectsUsed {resultSupport : A → Set T} {outputSupport : W → Set T}
    {a : A} (ha : ∀ (t : T) used, t ∈ used → resultSupport a ⊆ used)
    (hOne : outputSupport 1 = ∅) :
    (pure a : Alloc T W A).RespectsUsed resultSupport outputSupport :=
  Proofs.Semantics.ThreadTrace.pureRespectsUsed ha hOne

theorem bind_respectsUsed {supportA : A → Set T} {supportB : B → Set T}
    {outputSupport : W → Set T}
    (hMul : ∀ v w, outputSupport (v * w) ⊆ outputSupport v ∪ outputSupport w)
    {x : Alloc T W A} {k : A → Alloc T W B}
    (hx : x.RespectsUsed supportA outputSupport)
    (hk : ∀ a t used, t ∈ used → supportA a ⊆ used →
      ∀ b final w, ((b, final), w) ∈ (k a).run t used →
        used ⊆ final ∧ supportB b ⊆ final ∧ outputSupport w ⊆ final) :
    (x >>= k).RespectsUsed supportB outputSupport :=
  Proofs.Semantics.ThreadTrace.bindRespectsUsed hMul hx hk

theorem fresh_respectsUsed {outputSupport : W → Set T} (hOne : outputSupport 1 = ∅) :
    (fresh (W := W)).RespectsUsed (fun a => {a}) outputSupport :=
  Proofs.Semantics.ThreadTrace.freshRespectsUsed hOne

end Used

section Complete

variable [Monoid W] [Monoid V] (q : W →* V)

theorem Alloc.mem_saturate (x : Alloc T W A) (t : T) (used final : Set T) (a : A) (w : W) :
    ((a, final), w) ∈ (Alloc.saturate q x).run t used ↔
      ∃ w', ((a, final), w') ∈ x.run t used ∧ q w' = q w :=
  Proofs.Semantics.ThreadTrace.memSaturate q x t used final a w

theorem Alloc.mapOutput_saturate (x : Alloc T W A) :
    Alloc.mapOutput q (Alloc.saturate q x) = Alloc.mapOutput q x :=
  Proofs.Semantics.ThreadTrace.mapSaturate q x

theorem Alloc.saturate_idem (x : Alloc T W A) :
    Alloc.saturate q (Alloc.saturate q x) = Alloc.saturate q x :=
  Proofs.Semantics.ThreadTrace.saturateIdem q x

theorem Alloc.mapOutput_represent (hq : Function.Surjective q) (x : Alloc T V A) :
    Alloc.mapOutput q (Alloc.represent q x) = x :=
  Proofs.Semantics.ThreadTrace.mapRepresent q hq x

theorem Alloc.saturate_represent (x : Alloc T V A) :
    Alloc.saturate q (Alloc.represent q x) = Alloc.represent q x :=
  Proofs.Semantics.ThreadTrace.saturateRepresent q x

theorem Alloc.saturate_respectsUsed {resultSupport : A → Set T} {outputSupport : W → Set T}
    (hSupport : ∀ w w', q w = q w' → outputSupport w = outputSupport w')
    {x : Alloc T W A} (hx : x.RespectsUsed resultSupport outputSupport) :
    (Alloc.saturate q x).RespectsUsed resultSupport outputSupport :=
  Proofs.Semantics.ThreadTrace.saturateRespectsUsed q hSupport hx

theorem Complete.project_injective : Function.Injective (Complete.project (T := T) (A := A) q) :=
  Proofs.Semantics.ThreadTrace.projectInjective q

instance (T : Type u) : Monad (Complete T q) where
  pure a := ⟨Alloc.saturate q (pure a), Alloc.saturate_idem q _⟩
  bind x k := ⟨Alloc.saturate q (x.1 >>= fun a => (k a).1), Alloc.saturate_idem q _⟩

instance (T : Type u) : LawfulMonad (Complete T q) :=
  Proofs.Semantics.ThreadTrace.completeLawful q T

theorem Complete.val_pure (a : A) : (pure a : Complete T q A).1 = Alloc.saturate q (pure a) :=
  Proofs.Semantics.ThreadTrace.completePureVal q a

theorem Complete.val_bind (x : Complete T q A) (k : A → Complete T q B) :
    (x >>= k).1 = Alloc.saturate q (x.1 >>= fun a => (k a).1) :=
  Proofs.Semantics.ThreadTrace.completeBindVal q x k

theorem Complete.project_pure (a : A) : Complete.project q (pure a : Complete T q A) = pure a :=
  Proofs.Semantics.ThreadTrace.projectPure q a

theorem Complete.project_bind (x : Complete T q A) (k : A → Complete T q B) :
    Complete.project q (x >>= k) = Complete.project q x >>= fun a => Complete.project q (k a) :=
  Proofs.Semantics.ThreadTrace.projectBind q x k

theorem Complete.project_map (f : A → B) (x : Complete T q A) :
    Complete.project q (f <$> x) = f <$> Complete.project q x := by
  simp only [← bind_pure_comp, Complete.project_bind, Complete.project_pure]

/-- Projection and the lift of all quotient representatives are inverse. -/
@[expose] def Complete.equiv (hq : Function.Surjective q) : Complete T q A ≃ Alloc T V A where
  toFun := Complete.project q
  invFun x := ⟨Alloc.represent q x, Alloc.saturate_represent q x⟩
  left_inv x := Subtype.ext x.2
  right_inv := Alloc.mapOutput_represent q hq

theorem Complete.equiv_apply (hq : Function.Surjective q) (x : Complete T q A) :
    Complete.equiv q hq x = Complete.project q x := rfl

theorem Complete.equiv_symm_val (hq : Function.Surjective q) (x : Alloc T V A) :
    ((Complete.equiv q hq).symm x).1 = Alloc.represent q x := rfl

end Complete

section Renaming

open scoped Pointwise

variable [Monoid W] [MulDistribMulAction (Equiv.Perm T) W]

theorem fresh_equivariant : (fresh (T := T) (W := W)).Equivariant :=
  Proofs.Semantics.ThreadTrace.freshEquivariant

theorem alpha_used_result (t : T) (used : Set T) {a b : T} {s₁ s₂ : Set T} {w₁ w₂ : W}
    (ha : a ∈ used) (h : alpha t used ((a, s₁), w₁) = alpha t used ((b, s₂), w₂)) : b = a :=
  Proofs.Semantics.ThreadTrace.alphaUsedResult t used ha h

theorem fresh_alpha (t : T) (used : Set T) (ht : t ∈ used) {a b : T}
    (ha : a ∉ used) (hb : b ∉ used) :
    alpha t used ((a, insert a used), (1 : W)) = alpha t used ((b, insert b used), (1 : W)) :=
  Proofs.Semantics.ThreadTrace.freshAlpha t used ht ha hb

variable [MulAction (Equiv.Perm T) A] [MulAction (Equiv.Perm T) B]

theorem singleton_equivariant_iff (x : Det T W A) : (singleton x).Equivariant ↔ x.Equivariant :=
  Proofs.Semantics.ThreadTrace.singletonEquivariant x

theorem ignoreUsed_equivariant_iff (x : Nondet T W A) : (ignoreUsed x).Equivariant ↔ x.Equivariant :=
  Proofs.Semantics.ThreadTrace.ignoreUsedEquivariant x

theorem readOnly_equivariant_iff (x : ReadOnly T W A) : (readOnly x).Equivariant ↔ x.Equivariant :=
  Proofs.Semantics.ThreadTrace.readOnlyEquivariant x

theorem pure_equivariant (a : A) (ha : ∀ p : Equiv.Perm T, p • a = a) :
    (pure a : Alloc T W A).Equivariant :=
  Proofs.Semantics.ThreadTrace.pureEquivariant a ha

theorem bind_equivariant {x : Alloc T W A} {k : A → Alloc T W B} (hx : x.Equivariant)
    (hk : ∀ (p : Equiv.Perm T) (a : A) (t : T) (used : Set T) (b : Branch T W B),
      p • b ∈ (k (p • a)).run (p • t) (p • used) ↔ b ∈ (k a).run t used) :
    (x >>= k).Equivariant :=
  Proofs.Semantics.ThreadTrace.bindEquivariant hx hk

theorem Alloc.mapOutput_equivariant [Monoid V] [MulDistribMulAction (Equiv.Perm T) V]
    (q : W →* V) (hq : ∀ (p : Equiv.Perm T) w, q (p • w) = p • q w)
    {x : Alloc T W A} (hx : x.Equivariant) : (Alloc.mapOutput q x).Equivariant :=
  Proofs.Semantics.ThreadTrace.mapOutputEquivariant q hq hx

theorem Alloc.represent_equivariant [Monoid V] [MulDistribMulAction (Equiv.Perm T) V]
    (q : W →* V) (hq : ∀ (p : Equiv.Perm T) w, q (p • w) = p • q w)
    {x : Alloc T V A} (hx : x.Equivariant) : (Alloc.represent q x).Equivariant :=
  Proofs.Semantics.ThreadTrace.representEquivariant q hq hx

theorem Alloc.saturate_equivariant [Monoid V] [MulDistribMulAction (Equiv.Perm T) V]
    (q : W →* V) (hq : ∀ (p : Equiv.Perm T) w, q (p • w) = p • q w)
    {x : Alloc T W A} (hx : x.Equivariant) : (Alloc.saturate q x).Equivariant :=
  Alloc.represent_equivariant q hq (Alloc.mapOutput_equivariant q hq hx)

theorem fixing_used {t : T} {used : Set T} (p : fixing t used) :
    (p : Equiv.Perm T) • used = used :=
  Proofs.Semantics.ThreadTrace.fixingUsed p

theorem alpha_eq_iff (t : T) (used : Set T) (a b : Branch T W A) :
    alpha t used a = alpha t used b ↔ ∃ p : fixing t used, (p : Equiv.Perm T) • b = a :=
  Proofs.Semantics.ThreadTrace.alphaEq t used a b

theorem alpha_complete {x : Alloc T W A} (hx : x.Equivariant) (t : T) (used : Set T) :
    alpha t used ⁻¹' (alpha t used '' x.run t used) = x.run t used :=
  Proofs.Semantics.ThreadTrace.alphaComplete hx t used

end Renaming

end Silmaril.ThreadTrace

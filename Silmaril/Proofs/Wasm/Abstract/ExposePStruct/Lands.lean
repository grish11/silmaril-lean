module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: computations landing in a predicate
(`Lands`), their closure under binds and Elgot iteration, and conjugation of an iteration by a
map of its states (from uniformity and naturality).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct

variable {H : Type}

theorem stuck_bind' {X Y : Type 1} (g : X → M (CallSig H) H Y) :
    (stuck >>= g : M (CallSig H) H Y) = stuck := by
  funext s
  change ((stuck >>= g : M (CallSig H) H Y).run s) = (stuck : M (CallSig H) H Y).run s
  rw [StateT.run_bind]
  apply ExceptT.ext
  simp [stuck, ExceptT.run_bind, StateT.run, ExceptT.run_mk]

section Lands

variable {X Y : Type 1}

theorem lands_pure {P : X → Prop} {a : X} (h : P a) : Lands (H := H) P (pure a) :=
  ⟨pure ⟨a, h⟩, by rw [map_pure]⟩

theorem lands_stuck {P : X → Prop} : Lands (H := H) P stuck :=
  ⟨stuck, by rw [map_eq_bind_pure_comp, stuck_bind']⟩

theorem lands_trap {P : X → Prop} : Lands (H := H) P (trap ⟨⟩) :=
  ⟨trap ⟨⟩, by rw [map_eq_bind_pure_comp, Silmaril.Wasm.Abstract.Body.trap_bind]⟩

theorem lands_bind {P : X → Prop} {Q : Y → Prop} {x : M (CallSig H) H X}
    {k : X → M (CallSig H) H Y} (hx : Lands P x) (hk : ∀ a, P a → Lands Q (k a)) :
    Lands Q (x >>= k) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y >>= fun a => Classical.choose (hk a.1 a.2), ?_⟩
  rw [map_bind, bind_map_left]
  congr 1
  funext a
  exact Classical.choose_spec (hk a.1 a.2)

theorem lands_mono {P Q : X → Prop} {x : M (CallSig H) H X} (h : ∀ a, P a → Q a)
    (hx : Lands P x) : Lands Q x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(fun a => ⟨a.1, h a.1 a.2⟩) <$> y, by rw [Functor.map_map]⟩

theorem lands_true (x : M (CallSig H) H X) : Lands (fun _ => True) x :=
  ⟨(fun a => ⟨a, trivial⟩) <$> x, by rw [Functor.map_map]; exact (id_map x).symm⟩

theorem bind_congr_lands {P : X → Prop} {x : M (CallSig H) H X} {k k' : X → M (CallSig H) H Y}
    (hx : Lands P x) (h : ∀ a, P a → k a = k' a) : x >>= k = x >>= k' := by
  obtain ⟨y, rfl⟩ := hx
  rw [bind_map_left, bind_map_left]
  congr 1
  funext a
  exact h a.1 a.2

/-- A landing computation in a subtype of a sum, split into a sum of subtypes. -/
noncomputable def splitL {A B : Type 1} {PA : A → Prop} :
    {s : B ⊕ A // Sum.elim (fun _ => True) PA s} → B ⊕ {a // PA a}
  | ⟨.inl b, _⟩ => .inl b
  | ⟨.inr a, h⟩ => .inr ⟨a, h⟩

theorem splitL_val {A B : Type 1} {PA : A → Prop}
    (s : {s : B ⊕ A // Sum.elim (fun _ => True) PA s}) :
    Sum.map id Subtype.val (splitL s) = s.val := by
  rcases s with ⟨(b | a), h⟩ <;> rfl

/-- **Conjugating an iteration.** If every state of `PA` steps into `PA` (or exits), and the
step at `wA a` is the step at `a` with `wB` on exits and `wA` on states, the iteration from
`wA a` is the iteration from `a` followed by `wB`. -/
theorem iter_conj {A B : Type 1} (F : A → M (CallSig H) H (B ⊕ A)) (PA : A → Prop)
    (wA : A → A) (wB : B → B) (hF : ∀ a, PA a → Lands (Sum.elim (fun _ => True) PA) (F a))
    (hw : ∀ a, PA a → F (wA a) = Sum.map wB wA <$> F a) (a : A) (ha : PA a) :
    Silmaril.Elgot.iter F (wA a) = wB <$> Silmaril.Elgot.iter F a := by
  let F' : {a // PA a} → M (CallSig H) H (B ⊕ {a // PA a}) :=
    fun a => splitL <$> Classical.choose (hF a.1 a.2)
  have hF' : ∀ a : {a // PA a}, F a.1 = Sum.map id Subtype.val <$> F' a := by
    intro a
    rw [Classical.choose_spec (hF a.1 a.2)]
    simp only [F', Functor.map_map]
    congr 1
    funext s
    exact (splitL_val s).symm
  have hu1 := Silmaril.Elgot.LawfulElgotMonad.uniformity (m := M (CallSig H) H) F' F
    Subtype.val (by
      funext a
      simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def, pure_bind,
        hF' a, bind_pure_comp])
  let f2 : {a // PA a} → M (CallSig H) H (B ⊕ {a // PA a}) := fun a => Sum.map wB id <$> F' a
  have hu2 := Silmaril.Elgot.LawfulElgotMonad.uniformity (m := M (CallSig H) H) f2 F
    (wA ∘ Subtype.val) (by
      funext a
      simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def, pure_bind, f2,
        bind_pure_comp, Functor.map_map, hw a.1 a.2, hF' a]
      congr 1; funext s; rcases s with _ | _ <;> rfl)
  have hn := Silmaril.Elgot.LawfulElgotMonad.naturality (m := M (CallSig H) H) F'
    (Silmaril.Elgot.liftPure wB)
  have hmr : Silmaril.Elgot.mapReturn F' (Silmaril.Elgot.liftPure wB) = f2 := by
    funext a
    simp only [Silmaril.Elgot.mapReturn, Silmaril.Elgot.liftPure, f2, map_eq_bind_pure_comp]
    congr 1
    funext s
    rcases s with b | c <;> simp
  rw [hmr] at hn
  have e2 := congrFun hu2 ⟨a, ha⟩
  have e1 := congrFun hu1 ⟨a, ha⟩
  have en := congrFun hn ⟨a, ha⟩
  simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def, pure_bind] at e1 e2 en
  rw [← e2, ← en, e1, bind_pure_comp]

/-- **Iteration lands**: if every state of `PA` steps into `PA` or exits into `PB`, the
iteration from a state of `PA` exits into `PB`. -/
theorem lands_iter {A B : Type 1} (F : A → M (CallSig H) H (B ⊕ A)) (PA : A → Prop)
    (PB : B → Prop) (hF : ∀ a, PA a → Lands (Sum.elim PB PA) (F a)) (a : A) (ha : PA a) :
    Lands PB (Silmaril.Elgot.iter F a) := by
  let sp : {s : B ⊕ A // Sum.elim PB PA s} → {b // PB b} ⊕ {a // PA a}
    | ⟨.inl b, h⟩ => .inl ⟨b, h⟩
    | ⟨.inr a, h⟩ => .inr ⟨a, h⟩
  have hsp : ∀ s, Sum.map Subtype.val Subtype.val (sp s) = s.val := by
    rintro ⟨(b | a), h⟩ <;> rfl
  let F' : {a // PA a} → M (CallSig H) H ({b // PB b} ⊕ {a // PA a}) :=
    fun a => sp <$> Classical.choose (hF a.1 a.2)
  have hF' : ∀ a : {a // PA a}, F a.1 = Sum.map Subtype.val Subtype.val <$> F' a := by
    intro a
    rw [Classical.choose_spec (hF a.1 a.2)]
    simp only [F', Functor.map_map]
    congr 1
    funext s
    exact (hsp s).symm
  let f : {a // PA a} → M (CallSig H) H (B ⊕ {a // PA a}) := fun a => Sum.map Subtype.val id <$> F' a
  have hu := Silmaril.Elgot.LawfulElgotMonad.uniformity (m := M (CallSig H) H) f F
    Subtype.val (by
      funext a
      simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def, pure_bind, f,
        bind_pure_comp, Functor.map_map, hF' a]
      congr 1; funext s; rcases s with _ | _ <;> rfl)
  have hn := Silmaril.Elgot.LawfulElgotMonad.naturality (m := M (CallSig H) H) F'
    (Silmaril.Elgot.liftPure Subtype.val)
  have hmr : Silmaril.Elgot.mapReturn F' (Silmaril.Elgot.liftPure Subtype.val) = f := by
    funext a
    simp only [Silmaril.Elgot.mapReturn, Silmaril.Elgot.liftPure, f, map_eq_bind_pure_comp]
    congr 1
    funext s
    rcases s with b | c <;> simp
  rw [hmr] at hn
  refine ⟨Silmaril.Elgot.iter F' ⟨a, ha⟩, ?_⟩
  have e1 := congrFun hu ⟨a, ha⟩
  have en := congrFun hn ⟨a, ha⟩
  simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_def, pure_bind] at e1 en
  rw [← e1, ← en, bind_pure_comp]

end Lands

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct

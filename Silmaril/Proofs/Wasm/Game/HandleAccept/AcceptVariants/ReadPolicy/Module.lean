module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Defs

/-!
# `carCheck` meets its specification under the trapping and the typed-error read policies

Under `polISpec` with the read policy `trap` or `dflt errD`: an allowed answer `c ≠ -1` of
`car(a)` is the correct child (`pCar_post`: the error answer is the ill-typed `kind nil`, never
`handle c`), and an allowed answer `1` of `kind(a)` says that `a` is an atom (`pKind_post`: the
error answer of `kind` is the code `-1`). `carCheck_sat`: since `carCheck` returns on `-1`, it
meets the specification of `carAtomL` in every environment.

New proofs (no source).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Checkers Silmaril.Wasm.Game.HandleAccept.ReadPolicy
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The policy specification of the cons reader with error codes. -/
abbrev PSpec (I : ScalarInstance) (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32)))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (L : Set (SExp2 (BitVec 64))) : ISpec I.E :=
  polISpec (consR (BitVec 64) (BitVec 32)) pol (consDecAsk (ts := I.imports) consIx)
    (errDecAns consIx) ρ L

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

section Posts

variable {I : ScalarInstance} (hI : I.imports = consFTs)
  {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))}
  (hpol : pol = .trap ∨ pol = .dflt errD)
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hI

theorem p_pre_of_ne {k : Nat} (hk : k < 5) (h4 : k ≠ 4) (a : BitVec 32) :
    ∃ e, I.importOp? k [.i32 a] = some e ∧ (PSpec I pol ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_exists hI hk a
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [consDecAsk, consIx, h1, h4] at hd

theorem p_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 4 [.i32 a] = some e ∧ (PSpec I pol ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_exists hI (k := 4) (by omega) a
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [consDecAsk, consIx, h1, h2, i32Arg, Val.i32] at hd
  obtain rfl := hd
  exact hL

include hpol

variable {e : I.E.Op} {v : I.E.Ar e} {a : BitVec 32} {res : List Val}

/-- An allowed answer `c ≠ -1` of `car(a)` is correct. -/
theorem pCar_post (he : I.importOp? 1 [.i32 a] = some e) (hv : (PSpec I pol ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ (c ≠ -1 → ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some x) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, fun hc => ?_⟩
  have hd : errDecAns consIx e v = some (.read (.car a) (carAns c)) := by
    simp [errDecAns, consIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  obtain ⟨S, hS, haS⟩ := hv _ _ hd
  have hca : carAns c = .handle c := by
    unfold carAns
    split
    · contradiction
    · rfl
  rw [hca] at haS
  unfold answers at hS
  split at hS
  · cases hS; exact haS
  · rcases hpol with rfl | rfl <;> simp [badAnswers, errD] at hS <;> subst hS <;> simp at haS

/-- An allowed answer `1` of `kind(a)` says that `a` is an atom. -/
theorem pKind_post (he : I.importOp? 0 [.i32 a] = some e) (hv : (PSpec I pol ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ k, res = [.i32 k] ∧ (k = 1 → ∃ w, ρ a = some (.atom w)) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨k, rfl⟩ := res_i32 hty
  refine ⟨k, rfl, fun hk => ?_⟩
  subst hk
  have hd : errDecAns consIx e v = some (.read (.kind a) (kindAns 1)) := by
    simp [errDecAns, consIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  obtain ⟨S, hS, haS⟩ := hv _ _ hd
  have hka : kindAns (1 : BitVec 32) = (.kind .atom : ConsA (BitVec 64) (BitVec 32)) := by
    simp [kindAns]
  rw [hka] at haS
  unfold answers at hS
  split at hS
  · cases hS
    obtain ⟨x, hx, hk⟩ := haS
    cases x <;> cases hk
    exact ⟨_, hx⟩
  · rcases hpol with rfl | rfl <;> simp [badAnswers, errD] at hS <;> subst hS <;> simp at haS

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I consFTs aFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (consFTs.length + 1))
  {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))}
  (hpol : pol = .trap ∨ pol = .dflt errD)
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))} {a : BitVec 32}

include hS hs hm hpol

theorem X.pCar (hQ : Leaves Q s)
    (hc : ∀ c, (c ≠ -1 → ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some x) →
      HWP P (gameHost I (PSpec I pol ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (PSpec I pol ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  X.callG hS hs hm (k := 1) (by decide) rfl rfl (p_pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := pCar_post hS.imports hpol he hv hr
      exact hc c h) hQ

theorem X.pKind (hQ : Leaves Q s)
    (hc : ∀ k, (k = 1 → ∃ w, ρ a = some (.atom w)) →
      HWP P (gameHost I (PSpec I pol ρ L)) s f (vals (us ++ [.i32 k]) ++ expression is) Q) :
    HWP P (gameHost I (PSpec I pol ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  X.callG hS hs hm (k := 0) (by decide) rfl rfl (p_pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨k, rfl, h⟩ := pKind_post hS.imports hpol he hv hr
      exact hc k h) hQ

omit hpol in
theorem X.pAccept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (PSpec I pol ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (PSpec I pol ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.callG hS hs hm (k := 4) (by decide) rfl rfl (p_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := accept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## `carCheck` -/

theorem carCheck_shape : GShape (Verify.instOf carCheck) consFTs aFT [.i32]
    (carHead ++ errCheck ++ carTail) [some (.i32 0)] :=
  GShape.of_ok (by decide +kernel)

theorem args_aFT {args : List Val} (ht : List.Forall₂ ScalarType.HasVal aFT.params args) :
    ∃ h, args = [.i32 h] := by
  rcases ht with _ | ⟨⟨h, rfl⟩, hnil⟩
  cases hnil
  exact ⟨h, rfl⟩

/-- **`carCheck` meets the specification of `carAtomL`** under the trapping and the
typed-error read policies, in every environment and every profile. -/
theorem carCheck_sat (P : Profile)
    {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))}
    (hpol : pol = .trap ∨ pol = .dflt errD) (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf carCheck) (StoreInv (Verify.instOf carCheck))
      (PSpec (Verify.instOf carCheck) pol ρ carAtomL) (topISpec _) :=
  gameSat_ofG carCheck_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨h, rfl⟩ := args_aFT ht
    have hS := carCheck_shape
    simp only [carHead, errCheck, carTail, List.cons_append, List.nil_append]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.pCar (us := []) hS hs hm hpol hQ (fun c hc => ?_)
    refine X.localSet (by simp [Idx.toNat]) ?_
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.neConst ?_
    refine X.eqz ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h0 => ?_)
    have hc1 : c ≠ -1 := by
      intro hc
      subst hc
      revert h0
      decide
    obtain ⟨x, y, hxy, hcx⟩ := hc hc1
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.pKind hS hs hm hpol hQ (fun k hk => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h1 => ?_)
    have hk1 : k = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    obtain ⟨w, hw⟩ := hk hk1
    obtain rfl : x = .atom w := Option.some.inj (hcx.symm.trans hw)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.pAccept (us := []) hS hs hm (fun t ht' => ?_) hQ (X.done (hQn _))
    rw [hxy] at ht'
    cases ht'
    exact ⟨w, y, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy

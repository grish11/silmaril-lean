module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Defs

/-!
# The accept-variant modules meet their store specifications

Call rules for the seven imports of `variantsModule` under `storeISpec` (with a sentinel `sn`
that the environment `ρ` leaves undefined: a write's result then denotes nothing or the built
tree), and the Hoare-logic proofs:

* `errAccept_sat`: `errAccept` meets `storeISpec … ρ errL Set.univ`;
* `allAccept_sat`: `allAccept` meets `storeISpec … ρ allL allL` (every constructed tree is in
  `allL`);
* `batchAccept_sat`: `batchAccept` meets `storeISpec … ρ ∅ allL` (it accepts no handle; its
  constructed trees are in `allL`).

New proofs (no source).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.AcceptVariants
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `[] → [i32]`. -/
abbrev nilFT : FnType := ⟨[], [.num (.int .i32)]⟩
/-- `[i32 i32] → [i32]`. -/
abbrev consFT : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩
/-- `[i64] → [i32]`. -/
abbrev wordFT : FnType := ⟨[.num (.int .i64)], [.num (.int .i32)]⟩
/-- `[] → []`. -/
abbrev unitFT : FnType := ⟨[], []⟩
/-- `[i64] → []`. -/
abbrev runFT : FnType := ⟨[.num (.int .i64)], []⟩

/-- The import types of `variantsModule`. -/
abbrev variantsFTs : List FnType := [nilFT, consFT, wordFT, aFT, qFT, unitFT, aFT]

/-- The store specification of the variant modules. -/
abbrev SSpec (I : ScalarInstance) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (L C : Set (SExp2 (BitVec 64))) : ISpec I.E :=
  storeISpec (consW (BitVec 64)) sn (consXDecAsk (ts := I.imports) variantsIx)
    (consXDecAns variantsIx) ρ L C

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Questions and answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = variantsFTs) {sn : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L C : Set (SExp2 (BitVec 64))}

include hI

theorem s_op {k : Nat} (hk : k < 7) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (variantsFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e :=
  importOp?_existsG hI hk ht

/-- An answer of an import returning one `i32`. -/
theorem s_res_i32 {e : I.E.Op} {v : I.E.Ar e} {res : List Val} {k : Nat} {args : List Val}
    (hk : k < 7) (hty : (variantsFTs[k]'hk).results = [.num (.int .i32)])
    (he : I.importOp? k args = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ retI32 v = some r := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty', hans⟩ := results_ofG hI hr
  have : (variantsFTs[e.1.val]'(by simpa [hI] using e.1.2)).results = [.num (.int .i32)] := by
    simp only [h1]; exact hty
  rw [this] at hty'
  obtain ⟨r, rfl⟩ := res_i32 hty'
  exact ⟨r, rfl, by simp [retI32, hans, i32Res, Val.i32]⟩

/-- An answer of an import returning nothing. -/
theorem s_res_nil {e : I.E.Op} {v : I.E.Ar e} {res : List Val} {k : Nat} {args : List Val}
    (hk : k < 7) (hty : (variantsFTs[k]'hk).results = [])
    (he : I.importOp? k args = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty', -⟩ := results_ofG hI hr
  have : (variantsFTs[e.1.val]'(by simpa [hI] using e.1.2)).results = [] := by
    simp only [h1]; exact hty
  rw [this] at hty'
  exact res_nil hty'

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I variantsFTs runFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (variantsFTs.length + 1)) {sn : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} (hsn : ∀ r, sn = some r → ρ r = none)
  {L C : Set (SExp2 (BitVec 64))}

include hS hs hm hsn

/-- `nil()`, when `nil` is in the constructed-set bound. -/
theorem X.sNil (hC : SExp2.nil ∈ C) (hQ : Leaves Q s)
    (hc : ∀ r, (ρ r = none ∨ ρ r = some .nil) →
      HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := X.callG (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 0) (by decide) .nil
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        simp [Writer.built, Env.lookupAll, consW] at ht
        exact ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 0) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine hc r ?_
      have hd : consXDecAns variantsIx e v = some (.write .nil [] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr']
      rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
      · exact .inl (hsn r h)
      · simp [Writer.built, Env.lookupAll, consW] at ht
        exact .inr (hrt.trans (by rw [← ht]))) hQ
  simpa using h

/-- `word(x)`, when the word is in the constructed-set bound. -/
theorem X.sWord {x : BitVec 64} (hC : SExp2.atom x ∈ C) (hQ : Leaves Q s)
    (hc : ∀ r, (ρ r = none ∨ ρ r = some (.atom x)) →
      HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callG hS hs hm (k := 2) (by decide) rfl rfl (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 2) (by decide) (.cons ⟨x, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i64Arg] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        simp [Writer.built, Env.lookupAll, consW] at ht
        exact ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 2) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine hc r ?_
      have hd : consXDecAns variantsIx e v = some (.write (.atom x) [] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr', i64Arg, Val.i64]
      rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
      · exact .inl (hsn r h)
      · simp [Writer.built, Env.lookupAll, consW] at ht
        exact .inr (hrt.trans (by rw [← ht]))) hQ

/-- `cons(a, b)`, when the cell is in the constructed-set bound. -/
theorem X.sCons {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = none ∨ ρ a = some x)
    (hb : ρ b = none ∨ ρ b = some y) (hC : SExp2.cons x y ∈ C) (hQ : Leaves Q s)
    (hc : ∀ r, (ρ r = none ∨ ρ r = some (.cons x y)) →
      HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f
      (vals (us ++ [.i32 a, .i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  have hbuilt : ∀ t, (consW (BitVec 64)).built ρ .cons [a, b] = some t → t = .cons x y := by
    intro t ht
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [Writer.built, Env.lookupAll, ha, hb, consW] at ht
    exact ht.symm
  exact X.callG hS hs hm (k := 1) (by decide) rfl rfl (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 1) (by decide)
        (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil))
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Pair] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        exact hbuilt t ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 1) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine hc r ?_
      have hd : consXDecAns variantsIx e v = some (.write .cons [a, b] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr', i32Pair, Val.i32]
      rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
      · exact .inl (hsn r h)
      · exact .inr (hrt.trans (by rw [hbuilt t ht]))) hQ

omit hsn in
/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.sAccept {a : BitVec 32} (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG hS hs hm (k := 3) (by decide) rfl rfl (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 3) (by decide) (.cons ⟨a, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
        exact hd ▸ hL
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he _ res hr => by
      obtain rfl := s_res_nil hS.imports (k := 3) (by decide) rfl he hr
      simpa using hc) hQ

omit hsn in
/-- `accept_err(a)`, for `a` denoting (if anything) a member of `L`; any status follows. -/
theorem X.sAcceptErr {a : BitVec 32} (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : ∀ c : BitVec 32,
      HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.callG hS hs hm (k := 4) (by decide) rfl rfl (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 4) (by decide) (.cons ⟨a, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg] at hd
        obtain ⟨rfl, -⟩ := hd
        exact hL
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he _ res hr => by
      obtain ⟨c, rfl, -⟩ := s_res_i32 hS.imports (k := 4) (by decide) rfl he hr
      exact hc c) hQ

omit hsn in
/-- `accept_all()`. -/
theorem X.sAll (hCL : C ⊆ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals us ++ expression (.call ⟨5⟩ :: is)) Q := by
  have h := X.callG (us := us) (args := []) (x := ⟨5⟩) hS hs hm (k := 5) (by decide) rfl rfl
    (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 5) (by decide) .nil
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1, h2] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · exact hCL)
    (fun e v he _ res hr => by
      obtain rfl := s_res_nil hS.imports (k := 5) (by decide) rfl he hr
      simpa using hc) hQ
  simpa using h

omit hsn in
/-- `accept_batch(b)`. -/
theorem X.sBatch {b : BitVec 32} (hCL : b ≠ 0 → C ⊆ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (SSpec I sn ρ L C)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sn ρ L C)) s f
      (vals (us ++ [.i32 b]) ++ expression (.call ⟨6⟩ :: is)) Q :=
  X.callG hS hs hm (k := 6) (by decide) rfl rfl (Ii := SSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 6) (by decide) (.cons ⟨b, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1, h2] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
        exact hCL hd)
    (fun e v he _ res hr => by
      obtain rfl := s_res_nil hS.imports (k := 6) (by decide) rfl he hr
      simpa using hc) hQ

end Calls

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.AcceptVariants
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

theorem args_runFT {args : List Val} (ht : List.Forall₂ ScalarType.HasVal runFT.params args) :
    ∃ x, args = [.i64 x] := by
  rcases ht with _ | ⟨⟨x, rfl⟩, hnil⟩
  cases hnil
  exact ⟨x, rfl⟩

/-! ## `errAccept` -/

theorem err_shape : GShape (Verify.instOf errAccept) variantsFTs runFT [] errBody [] :=
  GShape.of_ok (by decide +kernel)

/-- **`errAccept` meets the store specification of `errL`** (no bound on the constructed set),
in every environment leaving the sentinel undefined. -/
theorem errAccept_sat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (hsn : ∀ r, sn = some r → ρ r = none) :
    GameSat P (Verify.instOf errAccept) (StoreInv (Verify.instOf errAccept))
      (SSpec (Verify.instOf errAccept) sn ρ errL Set.univ) (topISpec _) :=
  gameSat_ofG err_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := err_shape
    simp only [errBody]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.sWord (us := []) hS hs hm hsn trivial hQ (fun a ha => ?_)
    refine X.sAcceptErr (us := []) hS hs hm (fun t ht' => ?_) hQ (fun c => ?_)
    · rcases ha with ha | ha
      · rw [ha] at ht'; cases ht'
      · rw [ha] at ht'; cases ht'; exact .inl ⟨x, rfl⟩
    refine X.if_ (fun _ => ?_) (fun _ => X.done (hQn _))
    refine X.sNil (us := []) hS hs hm hsn trivial hQ.label (fun n hn => ?_)
    refine X.sAccept (us := []) hS hs hm (fun t ht' => ?_) hQ.label
      (X.blockEnd (X.done (hQn _)))
    rcases hn with hn | hn
    · rw [hn] at ht'; cases ht'
    · rw [hn] at ht'; cases ht'; exact .inr rfl

/-! ## `allAccept` -/

theorem all_shape : GShape (Verify.instOf allAccept) variantsFTs runFT [] allBody [] :=
  GShape.of_ok (by decide +kernel)

/-- **`allAccept` meets the store specification of `allL`**, its constructed set bounded by
`allL`. -/
theorem allAccept_sat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (hsn : ∀ r, sn = some r → ρ r = none) :
    GameSat P (Verify.instOf allAccept) (StoreInv (Verify.instOf allAccept))
      (SSpec (Verify.instOf allAccept) sn ρ allL allL) (topISpec _) :=
  gameSat_ofG all_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := all_shape
    simp only [allBody]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.sWord (us := []) hS hs hm hsn (.inl ⟨x, rfl⟩) hQ (fun a ha => ?_)
    refine X.sNil hS hs hm hsn (.inr (.inl rfl)) hQ (fun n hn => ?_)
    rw [show ([] : List Val) ++ [Val.i32 a] ++ [Val.i32 n] = [] ++ [Val.i32 a, Val.i32 n] from rfl]
    refine X.sCons (us := []) hS hs hm hsn ha hn (.inr (.inr ⟨x, rfl⟩)) hQ (fun c _ => ?_)
    refine Wp.drop (m := .part) ?_
    exact X.sAll hS hs hm le_rfl hQ (X.done (hQn _))

/-! ## `batchAccept` -/

theorem batch_shape : GShape (Verify.instOf batchAccept) variantsFTs runFT [] batchBody [] :=
  GShape.of_ok (by decide +kernel)

/-- **`batchAccept` meets the store specification of `allL`**, its constructed set bounded by
`allL`. -/
theorem batchAccept_sat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (hsn : ∀ r, sn = some r → ρ r = none) :
    GameSat P (Verify.instOf batchAccept) (StoreInv (Verify.instOf batchAccept))
      (SSpec (Verify.instOf batchAccept) sn ρ allL allL) (topISpec _) :=
  gameSat_ofG batch_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := batch_shape
    simp only [batchBody]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.sWord (us := []) hS hs hm hsn (.inl ⟨x, rfl⟩) hQ (fun a ha => ?_)
    refine X.i32Const ?_
    refine X.sBatch hS hs hm (fun _ => le_rfl) hQ ?_
    refine X.sNil hS hs hm hsn (.inr (.inl rfl)) hQ (fun n hn => ?_)
    rw [show ([] : List Val) ++ [Val.i32 a] ++ [Val.i32 n] = [] ++ [Val.i32 a, Val.i32 n] from rfl]
    refine X.sCons (us := []) hS hs hm hsn ha hn (.inr (.inr ⟨x, rfl⟩)) hQ (fun c _ => ?_)
    refine Wp.drop (m := .part) ?_
    refine X.i32Const ?_
    exact X.sBatch (us := []) hS hs hm (fun _ => le_rfl) hQ (X.done (hQn _))

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

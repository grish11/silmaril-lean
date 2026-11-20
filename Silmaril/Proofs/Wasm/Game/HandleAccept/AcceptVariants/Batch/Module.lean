module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Module
public import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Link
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.GhostRules

/-!
# Proofs: `batchAccept` meets the batch specification

* `GX.call`: **the import call rule under a ghost import specification**, for an instantiated
  module of shape `GShape`: in the store `gStore g sR`, the call of import `k` is allowed when
  its question meets `Gi.pre g`; every answer meeting `Gi.post` continues in
  `gStore (Gi.next (Gi.ask g e) e v) sR` (the environment does not write the store).
* `ghostGameSat_ofG`: a module of shape `GShape` meets a ghost import specification with the
  store invariant `StoreInv` (ghost unconstrained) if its body does, from every ghost.
* The call rules of `batchAccept` under `batchGSpec`, tracking the current batch: `word`,
  `nil`, `cons` add (at most) the tree they build, `accept_batch` empties the batch and may keep
  it only when it is in `L`.
* `batchAccept_gsat`: `batchAccept` meets `batchGSpec … ρ keptL allL`: when it calls
  `accept_batch(1)`, the batch holds at most `nil` and the cell `(x)` built after
  `accept_batch(0)` dropped the word.

New proofs (no source).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.AcceptVariants
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost (gStore ghostH)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost (gStore_inj gStore_funcs GX.localGet
  GX.i32Const GX.done)
open Silmaril.Proofs.Wasm.Component.Reference (FuncInst.mapH FuncCode.mapH)

variable {G : Type} {P : Profile}

/-! ## The call rule and the export rule -/

/-- `Q` accepts returns, traps and exceptions in every store carrying a ghost whose functions
are those of the instance. -/
def GLeaves (I : ScalarInstance) (Q : Post (Nat × G)) : Prop :=
  ∀ g sR, sR.funcs = I.store.funcs → ∀ f, (∀ vs, Q (gStore g sR) f (.ret vs)) ∧
    Q (gStore g sR) f .trap ∧ ∀ a, Q (gStore g sR) f (.throw a)

section Calls

variable {I : ScalarInstance} {fts : List FnType} {eft : FnType} {locals : List ValType}
  {body : List Instr} {D : List (Option Val)}

/-- **The import call rule under a ghost import specification.** -/
theorem GX.call (hS : GShape I fts eft locals body D) {Gi : GISpec I.E G} {g : G}
    {sR : Store Nat} (hs : sR.funcs = I.store.funcs) {f : Frame}
    (hm : f.module.funcs = List.range (fts.length + 1)) {k : Nat} (hk : k < fts.length)
    {x : FuncIdx} (hx : x.toNat = k) {args : List Val}
    (hargs : (fts[k]'hk).params.length = args.length) {us : List Val} {is : List Instr}
    {Q : Post (Nat × G)}
    (hop : ∃ e, I.importOp? k args = some e ∧ Gi.pre g e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Gi.post (Gi.ask g e) e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (ghostHost I Gi) (gStore (Gi.next (Gi.ask g e) e v) sR) f
          (vals (us ++ res) ++ expression is) Q)
    (hQ : GLeaves I Q) :
    HWP P (ghostHost I Gi) (gStore g sR) f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
    have hf' : sR.funcs[k]? = some fk := by rw [hs]; exact hf
    have hxk : f.module.funcs[x.toNat]? = some k := by
      rw [hm, hx, List.getElem?_range (by omega)]
    have hS' : ghostCtx I Gi (Prod.fst (k, g)) = some (ghostImportSpec I Gi k) := rfl
    have hfg : (gStore g sR).funcs[k]? = some (FuncInst.mapH (ghostH g) fk) := by
      rw [gStore_funcs, hf']; rfl
    have hcg : (FuncInst.mapH (ghostH g) fk).code = .host (k, g) := by
      simp [FuncInst.mapH, hcode, FuncCode.mapH, ghostH]
    refine Safe.callIdx (x := x)
      (S := Silmaril.Wasm.Logic.Open.stubSpec k (k, g) (ghostImportSpec I Gi k)) hxk hfg
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS' n)
      ⟨⟨_, ps, rs, hfg, hcg, he, (hps.trans hargs).symm⟩, ⟨g, sR, rfl, hop⟩⟩ ?_
    obtain ⟨e, hop', -⟩ := hop
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩ <;>
      obtain ⟨g₁, sR₁, hs₁, hR⟩ := hR <;>
      obtain ⟨rfl, rfl⟩ := gStore_inj hs₁ hf' hcode <;>
      obtain ⟨v, hv, ho, rfl⟩ := hR e hop'
    · rcases hr : Answer.toResult (ft := I.imports.get e.1) v with vs | a | _ <;>
        rw [hr] at ho <;> simp [resultOutcome] at ho
      subst ho
      exact hc e v hop' hv vs hr n
    · exact (hQ _ _ hs f).2.1
    · exact (hQ _ _ hs f).2.2 y

/-- **A module of shape `GShape` meets a ghost import specification** if its body does, from
the frame of a call on any typed arguments, in every ghost. -/
theorem ghostGameSat_ofG (hS : GShape I fts eft locals body D) (hr : eft.results = [])
    (h0 : 0 < fts.length) {Gi : GISpec I.E G}
    (hbody : ∀ (fi : FuncInst Nat) (g : G) (sR : Store Nat) (args : List Val)
      (Q : Post (Nat × G)), List.Forall₂ ScalarType.HasVal eft.params args →
      I.store.funcs[fts.length]? = some fi → fi.module.funcs = List.range (fts.length + 1) →
      sR.funcs = I.store.funcs → GLeaves I Q →
      (∀ g sR, sR.funcs = I.store.funcs → ∀ f, Q (gStore g sR) f (.normal [])) →
      HWP P (ghostHost I Gi) (gStore g sR) ⟨args.map some ++ D, fi.module⟩
        (vals [] ++ expression body) Q) :
    GhostGameSat P I Gi (fun _ s => s.funcs = I.store.funcs) := by
  intro j
  rw [hS.addr j]
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := hS.fn
  have hl : I.exports.length = 1 := by rw [hS.exports]; rfl
  have hg : I.exports.get j = eft := by
    rw [List.get_eq_getElem, List.getElem_of_eq hS.exports j.2]
    have hj : j.val = 0 := by have := j.2; omega
    simp only [hj]
    rfl
  have hrs0 : rs.length = 0 := by rw [hrs, hr]; rfl
  obtain ⟨f0, -, -, hf0, hc0, -⟩ := hS.stub 0 h0
  let fiS : FuncInst (Nat × G) := ⟨fi.type, fi.module, .wasm code⟩
  have hfiS : ∀ g sR, sR.funcs = I.store.funcs → (gStore g sR).funcs[fts.length]? = some fiS := by
    intro g sR h
    rw [gStore_funcs, h, hf]
    simp [fiS, FuncInst.mapH, hcode, FuncCode.mapH]
  have hpost : ∀ (g : G) (sR : Store Nat), sR.funcs = I.store.funcs →
      ∀ (s₀ : Store (Nat × G)) (args : List Val) (o : Outcome),
      (ghostExportSpec (G := G) I (fun _ s => s.funcs = I.store.funcs) j).post s₀ args
        (gStore g sR) o := by
    intro g sR h s₀ args o g' sR' heq
    have hf0' : sR.funcs[0]? = some f0 := by rw [h]; exact hf0
    obtain ⟨rfl, rfl⟩ := gStore_inj heq hf0' hc0
    exact h
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fiS) (fun s args hpre => ?_) rfl he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨g, sR, rfl, hInv, -⟩ := hpre
      exact hfiS g sR hInv
    · obtain ⟨-, -, -, -, ht⟩ := hpre
      rw [hg] at ht
      rw [hps, ht.length_eq]
    · obtain ⟨g, sR, rfl, hInv, ht⟩ := hpre
      have ht' := ht
      rw [hg] at ht'
      have hfr : Frame.forCall fiS.module args code.locals = ⟨args.map some ++ D, fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
      rw [hfr, hbod]
      refine hbody fi g sR args _ ht' hf hm hInv (fun g' sR' hs' F => ?_)
        (fun g' sR' hs' F => ?_) n
      · refine ⟨fun vs => ?_, ⟨rfl, .inr (.inl ⟨rfl, hpost g' sR' hs' _ _ _⟩)⟩,
          fun a => ⟨rfl, .inr (.inr ⟨a, rfl, hpost g' sR' hs' _ _ _⟩)⟩⟩
        exact ⟨[] ++ vs, [], by simp, by simp [hrs0], rfl, .inl ⟨[], by simp,
          hpost g' sR' hs' _ _ _⟩⟩
      · exact ⟨by simp [hrs0], rfl, .inl ⟨[], by simp, hpost g' sR' hs' _ _ _⟩⟩

end Calls

/-! ## The calls of `batchAccept` under the batch specification -/

/-- The batch specification of the variant modules. -/
abbrev BSpec (I : ScalarInstance) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (L C : Set (SExp2 (BitVec 64))) :
    GISpec I.E (Set (SExp2 (BitVec 64))) :=
  batchGSpec (consW (BitVec 64)) sn (consXDecAsk (ts := I.imports) variantsIx)
    (consXDecAns variantsIx) ρ L C

section Rules

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I variantsFTs runFT locals body D) {sR : Store Nat}
  (hs : sR.funcs = I.store.funcs) {f : Frame}
  (hm : f.module.funcs = List.range (variantsFTs.length + 1)) {sn : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} (hsn : ∀ r, sn = some r → ρ r = none)
  {L C : Set (SExp2 (BitVec 64))} {g : Set (SExp2 (BitVec 64))} {us : List Val}
  {is : List Instr} {Q : Post (Nat × Set (SExp2 (BitVec 64)))}

include hS hs hm hsn

/-- `word(x)`: the batch gains (at most) the word. -/
theorem GX.bWord {x : BitVec 64} (hC : SExp2.atom x ∈ C) (hQ : GLeaves I Q)
    (hc : ∀ r g', (ρ r = none ∨ ρ r = some (.atom x)) → g' ⊆ insert (.atom x) g →
      HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g' sR) f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g sR) f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  GX.call hS hs hm (k := 2) (by decide) rfl rfl (Gi := BSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 2) (by decide) (.cons ⟨x, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_, fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i64Arg] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        simp [Writer.built, Env.lookupAll, consW] at ht
        exact ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 2) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      have hd : consXDecAns variantsIx e v = some (.write (.atom x) [] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr', i64Arg, Val.i64]
      have ha : consXDecAsk (ts := I.imports) variantsIx e = none := by
        simp [consXDecAsk, variantsIx, h1]
      refine hc r _ ?_ ?_
      · rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
        · exact .inl (hsn r h)
        · simp [Writer.built, Env.lookupAll, consW] at ht
          exact .inr (hrt.trans (by rw [← ht]))
      · intro t ht
        simp [batchGSpec, ha, hd, batchGhost, Writer.built, Env.lookupAll, consW] at ht ⊢
        tauto) hQ

/-- `nil()`: the batch gains (at most) `nil`. -/
theorem GX.bNil (hC : SExp2.nil ∈ C) (hQ : GLeaves I Q)
    (hc : ∀ r g', (ρ r = none ∨ ρ r = some .nil) → g' ⊆ insert .nil g →
      HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g' sR) f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g sR) f
      (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := GX.call (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (Gi := BSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 0) (by decide) .nil
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_, fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;> simp [consXDecAns, variantsIx, h1, h2, hrv] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        simp [Writer.built, Env.lookupAll, consW] at ht
        exact ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 0) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      have hd : consXDecAns variantsIx e v = some (.write .nil [] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr']
      have ha : consXDecAsk (ts := I.imports) variantsIx e = none := by
        simp [consXDecAsk, variantsIx, h1]
      refine hc r _ ?_ ?_
      · rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
        · exact .inl (hsn r h)
        · simp [Writer.built, Env.lookupAll, consW] at ht
          exact .inr (hrt.trans (by rw [← ht]))
      · intro t ht
        simp [batchGSpec, ha, hd, batchGhost, Writer.built, Env.lookupAll, consW] at ht ⊢
        tauto) hQ
  simpa using h

/-- `cons(a, b)`: the batch gains (at most) the cell. -/
theorem GX.bCons {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = none ∨ ρ a = some x)
    (hb : ρ b = none ∨ ρ b = some y) (hC : SExp2.cons x y ∈ C) (hQ : GLeaves I Q)
    (hc : ∀ r g', (ρ r = none ∨ ρ r = some (.cons x y)) → g' ⊆ insert (.cons x y) g →
      HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g' sR) f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g sR) f
      (vals (us ++ [.i32 a, .i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  have hbuilt : ∀ t, (consW (BitVec 64)).built ρ .cons [a, b] = some t → t = .cons x y := by
    intro t ht
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [Writer.built, Env.lookupAll, ha, hb, consW] at ht
    exact ht.symm
  exact GX.call hS hs hm (k := 1) (by decide) rfl rfl (Gi := BSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 1) (by decide)
        (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil))
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_, fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Pair] at hd
        obtain ⟨rfl, rfl, -⟩ := hd
        exact hbuilt t ht ▸ hC
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd)
    (fun e v he hv res hr => by
      obtain ⟨r, rfl, hr'⟩ := s_res_i32 hS.imports (k := 1) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      have hd : consXDecAns variantsIx e v = some (.write .cons [a, b] r) := by
        simp [consXDecAns, variantsIx, h1, h2, hr', i32Pair, Val.i32]
      have hda : consXDecAsk (ts := I.imports) variantsIx e = none := by
        simp [consXDecAsk, variantsIx, h1]
      refine hc r _ ?_ ?_
      · rcases hv _ _ _ hd with h | ⟨t, ht, hrt⟩
        · exact .inl (hsn r h)
        · exact .inr (hrt.trans (by rw [hbuilt t ht]))
      · intro t ht
        simp [BSpec, batchGSpec, hda, hd, batchGhost] at ht
        rcases ht with ht | ht
        · exact Set.mem_insert_of_mem _ ht
        · exact hbuilt t ht ▸ Set.mem_insert _ _) hQ

omit hsn in
/-- `accept_batch(b)`: allowed with `b ≠ 0` only when the batch is in `L`; the batch is then
empty. -/
theorem GX.bBatch {b : BitVec 32} (hCL : b ≠ 0 → g ⊆ L) (hQ : GLeaves I Q)
    (hc : HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore ∅ sR) f (vals us ++ expression is) Q) :
    HWP P (ghostHost I (BSpec I sn ρ L C)) (gStore g sR) f
      (vals (us ++ [.i32 b]) ++ expression (.call ⟨6⟩ :: is)) Q :=
  GX.call hS hs hm (k := 6) (by decide) rfl rfl (Gi := BSpec I sn ρ L C) (by
      obtain ⟨e, he⟩ := s_op hS.imports (k := 6) (by decide) (.cons ⟨b, rfl⟩ .nil)
      obtain ⟨h1, h2⟩ := importOp?_eq he
      refine ⟨e, he, fun h hd => ?_, fun v h b hd => ?_, fun v op args r hd t ht => ?_,
        fun hd => ?_, fun hd => ?_⟩
      · simp [consXDecAsk, variantsIx, h1, h2] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
      · simp [consXDecAsk, variantsIx, h1, h2, i32Arg] at hd
        exact hCL hd)
    (fun e v he _ res hr => by
      obtain rfl := s_res_nil hS.imports (k := 6) (by decide) rfl he hr
      obtain ⟨h1, h2⟩ := importOp?_eq he
      have hda : consXDecAsk (ts := I.imports) variantsIx e = some (.acceptBatch (b != 0)) := by
        simp [consXDecAsk, variantsIx, h1, h2, i32Arg, Val.i32]
      have hd : consXDecAns variantsIx e v = none := by
        rcases hrv : retI32 v with _ | r' <;>
          simp [consXDecAns, variantsIx, h1, h2, hrv, i32Arg, i64Arg, i32Pair]
      have hgst : (BSpec I sn ρ L C).next ((BSpec I sn ρ L C).ask g e) e v = ∅ := by
        simp [BSpec, batchGSpec, hda, hd, batchGhost]
      rw [hgst]
      simpa using hc) hQ

end Rules

/-! ## `batchAccept` -/

/-- **`batchAccept` meets the batch specification of `keptL`**, its constructed set bounded by
`allL`, in every environment leaving the sentinel undefined. -/
theorem batchAccept_gsat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (hsn : ∀ r, sn = some r → ρ r = none) :
    GhostGameSat P (Verify.instOf batchAccept) (BSpec (Verify.instOf batchAccept) sn ρ keptL allL)
      (fun _ s => s.funcs = (Verify.instOf batchAccept).store.funcs) :=
  ghostGameSat_ofG batch_shape rfl (by decide) fun fi g sR args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := batch_shape
    simp only [batchBody]
    refine GX.localGet (v := .i64 x) rfl ?_
    refine GX.bWord (us := []) hS hs hm hsn (.inl ⟨x, rfl⟩) hQ (fun a g₁ ha _ => ?_)
    refine GX.i32Const ?_
    refine GX.bBatch hS hs hm (fun h => absurd rfl h) hQ ?_
    refine GX.bNil hS hs hm hsn (.inr (.inl rfl)) hQ (fun n g₂ hn hg₂ => ?_)
    rw [show ([] : List Val) ++ [Val.i32 a] ++ [Val.i32 n] = [] ++ [Val.i32 a, Val.i32 n] from rfl]
    refine GX.bCons (us := []) hS hs hm hsn ha hn (.inr (.inr ⟨x, rfl⟩)) hQ
      (fun c g₃ _ hg₃ => ?_)
    refine Wp.drop (m := .part) ?_
    refine GX.i32Const ?_
    refine GX.bBatch (us := []) hS hs hm (fun _ t ht => ?_) hQ (GX.done (hQn _ _ hs _))
    rcases hg₃ ht with rfl | ht
    · exact .inr ⟨x, rfl⟩
    · rcases hg₂ ht with rfl | ht
      · exact .inl rfl
      · exact absurd ht (Set.notMem_empty _)

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch

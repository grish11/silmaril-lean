module

public import Silmaril.WasmSpec.BTree.V2.Defs
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# The B-tree library, version 2: `oba_get` and `oba_find` by tactics

As in version 1 (`Silmaril.Proofs.WasmSpec.BTree.Tactic`, whose proofs these are, adapted):
symbolic execution with the rules of `Silmaril.Wasm.Logic.Words`; `oba_get` needs only a bounded
array (it is also used on the unordered pointer arrays); `oba_find`'s loop has the paper's
invariant (Figure 13: every element before `i` is below `e`) and the variant `|α| + 1 - i`.
Every-run total correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem getFunc_body : getFunc.body = [lget 0, lget 1, c32 4, imul, iadd,
    .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩] := rfl

theorem findFunc_body : findFunc.body = [while_ [lget 2, lget 0, iload, igeu, brIf 1,
    lget 0, lget 2, c32 4, imul, iadd, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, lget 1, .intRelOp .i32 (.ge .signed),
    brIf 1, lget 2, c32 1, iadd, lset 2, br 0], lget 2] := rfl

theorem forCall_get (mi : ModuleInst) (x k : BitVec 32) :
    Frame.forCall mi [.i32 x, .i32 k] getFunc.locals = fr mi [x, k] := rfl

theorem forCall_find (mi : ModuleInst) (x e : BitVec 32) :
    Frame.forCall mi [.i32 x, .i32 e] findFunc.locals = fr mi [x, e, 0] := rfl

/-- Element `k` of an `OBA`, read at `x + 4 k + 4`. -/
theorem BA.wd_elem {B : ByteArray} {x n : Nat} {α : List (BitVec 32)} (h : BA B x n α)
    {xb k : BitVec 32} (hx : xb.toNat = x) (hk : k.toNat < α.length) :
    wd B ((xb + k * 4#32).toNat + 4) = α.getD k.toNat 0 := by
  obtain ⟨-, hw, hn, hmax, -⟩ := h
  have hmax' : x + 4 + 4 * n ≤ 2 ^ 31 - 1 := hmax
  have ha : (xb + k * 4#32).toNat = x + 4 * k.toNat := by
    rw [addr_toNat (n := n) (by omega) (by omega), hx]
  rw [ha, show x + 4 * k.toNat + 4 = x + 4 + 4 * k.toNat by omega, ← getD_words hk, hw]

/-- The length cell of a `BA`. -/
theorem BA.len {B : ByteArray} {x n : Nat} {α : List (BitVec 32)} (h : BA B x n α) :
    (wd B x).toNat = α.length := by
  rw [h.1, BitVec.toNat_ofNat]
  have hmax' : x + 4 + 4 * n ≤ 2 ^ 31 - 1 := h.2.2.2.1
  exact Nat.mod_eq_of_lt (by have := h.2.2.1; omega)

/-- A bounded array's contents are determined by the memory. -/
theorem BA.unique {B : ByteArray} {x n n' : Nat} {α α' : List (BitVec 32)} (h : BA B x n α)
    (h' : BA B x n' α') : α' = α := by
  have hl : α'.length = α.length := h'.len.symm.trans h.len
  rw [← h'.2.1, ← h.2.1, hl]

/-- The postcondition of `oba_get` for the value read. -/
theorem get_post {a : Nat} {fi : FuncInst H} {s : Store H} {x k : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {n : Nat} {α : List (BitVec 32)}
    (hm : MemAt s fi.module ma mt B) (hO : BA B x.toNat n α) :
    (getSpec a fi).post s [.i32 x, .i32 k] s (.normal [.i32 (α.getD k.toNat 0)]) := by
  refine ⟨rfl, fun x' k' ma' mt' B' n' α' hargs hm' hO' _ => ?_⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain rfl := i32_inj hargs.1
  obtain rfl := i32_inj hargs.2
  obtain ⟨-, -, rfl⟩ := hm'.unique hm
  rw [hO'.unique hO]

/-- The body of `oba_get`. -/
theorem get_body {s : Store H} {mi : ModuleInst} {x k : BitVec 32} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {n : Nat} {α : List (BitVec 32)} (hm : MemAt s mi ma mt B)
    (hO : BA B x.toNat n α) (hk : k.toNat < α.length) {Q : Post H}
    (hQ : Q s (fr mi [x, k]) (.normal [.i32 (α.getD k.toNat 0)])) :
    TWP P host s (fr mi [x, k]) (vals [] ++ expression [lget 0, lget 1, c32 4, imul, iadd,
      .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩]) Q := by
  have hv := hO.wd_elem rfl hk
  obtain ⟨-, -, hn, hmax, hb⟩ := hO
  have hmax' : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hmax
  have ha : (x + k * 4#32).toNat = x.toNat + 4 * k.toNat := addr_toNat (n := n) (by omega) (by omega)
  wbegin
  wrun
  rw [show wd B ((x + k * 4#32).toNat + ((4 : Fin (2 ^ 64)) : Nat)) = α.getD k.toNat 0 from hv]
  exact w_end (m := .total) (rs := [Val.i32 (α.getD k.toNat 0)]) hQ

/-- **`oba_get` meets `getSpec`.** -/
theorem get_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm getFunc)
    (har : HasArity fi 2 1) : TFSpecAt P host a (getSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, x, k, ma, mt, B, n, α, rfl, -⟩
    simp [hps]
  · rintro s args ⟨-, x, k, ma, mt, B, n, α, rfl, hm, hO, hk⟩ f vs₀
    rw [forCall_get, getFunc_body]
    exact get_body hm hO hk (bodyPostT_normal (by simp [hrs]) (get_post hm hO))

/-! ## `oba_find` -/

/-- **The loop invariant of `oba_find`** (the paper's `P_inv`, Figure 13). -/
def FInv (s₀ : Store H) (mi : ModuleInst) (x e : BitVec 32) (α : List (BitVec 32)) (s : Store H)
    (f : Frame) : Prop :=
  s = s₀ ∧ ∃ i : BitVec 32, f = fr mi [x, e, i] ∧ i.toNat ≤ α.length ∧
    ∀ j < i.toNat, (α.getD j 0).toInt < e.toInt

/-- The variant `|α| + 1 - i`. -/
def FV (α : List (BitVec 32)) (_ : Store H) (f : Frame) : Nat := α.length + 1 - loc f 2

/-- After the loop: return `i`. -/
theorem find_after {s₀ : Store H} {mi : ModuleInst} {x e i : BitVec 32} {α : List (BitVec 32)}
    {Q : Post H} (hQ : ∀ i', FindsAt α e i' → ∀ F, Q s₀ F (.normal [.i32 (BitVec.ofNat 32 i')]))
    (hF : FindsAt α e i.toNat) :
    TWP P host s₀ (fr mi [x, e, i]) (vals [] ++ expression [lget 2]) Q := by
  wbegin
  wrun
  refine w_end (m := .total) (rs := [Val.i32 i]) ?_
  have hq := hQ i.toNat hF (fr mi [x, e, i])
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hq
  exact hq

/-- In a sorted list, a later element is at least an earlier one. -/
theorem sortedS_getD_le {α : List (BitVec 32)} (hs : SortedS α) {i j : Nat} (hij : i ≤ j)
    (hj : j < α.length) : (α.getD i 0).toInt ≤ (α.getD j 0).toInt := by
  rw [getD_of_lt _ (by omega), getD_of_lt _ hj]
  rcases Nat.lt_or_ge i j with h | h
  · exact sortedS_iff_getElem.1 hs i j (by omega) hj h
  · have : i = j := by omega
    subst this
    exact le_refl _

/-- The comparison `α!i ≥ e`, for `i < |α|`. -/
theorem find_cmp {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {x e i : BitVec 32} {n : Nat} {α : List (BitVec 32)} (hm : MemAt s mi ma mt B)
    (hO : OBA B x.toNat n α) {Q : Post H}
    (hQ : ∀ i', FindsAt α e i' → ∀ F, Q s F (.normal [.i32 (BitVec.ofNat 32 i')]))
    (hil : i.toNat < α.length) (hi : i.toNat ≤ α.length)
    (hlt : ∀ j < i.toNat, (α.getD j 0).toInt < e.toInt) :
    TWP P host s (fr mi [x, e, i]) (vals ([] : List Val).reverse ++ expression [
        lget 0, lget 2, c32 4, imul, iadd, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, lget 1,
        .intRelOp .i32 (.ge .signed), brIf 1, lget 2, c32 1, iadd, lset 2, br 0])
      (whilePostT P host (FInv s mi x e α) (FV α) (α.length + 1 - i.toNat)
        (expression [lget 2]) Q) := by
  have hv := hO.1.wd_elem rfl hil
  obtain ⟨-, -, hn, hmax, hb⟩ := hO.1
  have hmax' : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hmax
  have ha : (x + i * 4#32).toNat = x.toNat + 4 * i.toNat := addr_toNat (n := n) (by omega) (by omega)
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hV : FV α s (fr mi [x, e, i + 1#32]) < α.length + 1 - i.toNat := by
    simp only [FV, loc_fr (L := [x, e, i + 1#32]) (k := 2) (by simp), List.getD_cons_succ,
      List.getD_cons_zero]
    omega
  wbegin
  wrun
  rw [show wd B ((x + i * 4#32).toNat + ((4 : Fin (2 ^ 64)) : Nat)) = α.getD i.toNat 0 from hv]
  have hinv : (α.getD i.toNat 0).toInt < e.toInt →
      ∀ j < (i + 1#32).toNat, (α.getD j 0).toInt < e.toInt := fun hlt' j hj => by
    rcases Nat.lt_or_ge j i.toNat with h | h
    · exact hlt j h
    · have : j = i.toNat := by omega
      rw [this]
      exact hlt'
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : e.toInt ≤ (α.getD i.toNat 0).toInt := by simpa using hc
    exact whilePostT_exit (find_after hQ ⟨hi, hlt, fun j hj hj' =>
      le_trans hge (sortedS_getD_le hO.2 hj hj')⟩)
  · have hlt' : (α.getD i.toNat 0).toInt < e.toInt := by simpa using hc
    wrun
    exact t_br (whilePostT_cont ⟨rfl, i + 1#32, rfl, by omega, hinv hlt'⟩ hV)

/-- **One iteration of `oba_find`'s loop.** -/
theorem find_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {x e : BitVec 32} {n : Nat} {α : List (BitVec 32)} (hm : MemAt s₀ mi ma mt B)
    (hO : OBA B x.toNat n α) {Q : Post H}
    (hQ : ∀ i', FindsAt α e i' → ∀ F, Q s₀ F (.normal [.i32 (BitVec.ofNat 32 i')]))
    {s : Store H} {f : Frame} (hI : FInv s₀ mi x e α s f) :
    TWP P host s f (vals [] ++ expression [lget 2, lget 0, iload, igeu, brIf 1,
        lget 0, lget 2, c32 4, imul, iadd, .intLoad .i32 none ⟨0⟩ ⟨2, 4⟩, lget 1,
        .intRelOp .i32 (.ge .signed), brIf 1, lget 2, c32 1, iadd, lset 2, br 0])
      (whilePostT P host (FInv s₀ mi x e α) (FV α) (FV α s f) (expression [lget 2]) Q) := by
  obtain ⟨rfl, i, rfl, hi, hlt⟩ := hI
  have hlen : (wd B x.toNat).toNat = α.length := hO.1.len
  have hV : FV α s (fr mi [x, e, i]) = α.length + 1 - i.toNat := by
    simp only [FV, loc_fr (L := [x, e, i]) (k := 2) (by simp), List.getD_cons_succ,
      List.getD_cons_zero]
  obtain ⟨-, -, hn, hmax, hb⟩ := hO.1
  have hmax' : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hmax
  rw [hV]
  wbegin
  wrun
  rw [hlen]
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : α.length ≤ i.toNat := by simpa using hc
    exact whilePostT_exit (find_after hQ ⟨hi, hlt, fun j hj hj' => absurd hj' (by omega)⟩)
  · have hil : i.toNat < α.length := by simpa using hc
    exact find_cmp hm hO hQ hil hi hlt

/-- The postcondition of `oba_find` for an index it finds. -/
theorem find_post {a : Nat} {fi : FuncInst H} {s : Store H} {x e : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {n : Nat} {α : List (BitVec 32)}
    (hm : MemAt s fi.module ma mt B) (hO : OBA B x.toNat n α) {i : Nat} (hF : FindsAt α e i) :
    (findSpec a fi).post s [.i32 x, .i32 e] s (.normal [.i32 (BitVec.ofNat 32 i)]) := by
  refine ⟨rfl, fun x' e' ma' mt' B' n' α' hargs hm' hO' => ?_⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain rfl := i32_inj hargs.1
  obtain rfl := i32_inj hargs.2
  obtain ⟨-, -, rfl⟩ := hm'.unique hm
  have hα : α' = α := hO.1.unique hO'.1
  exact ⟨i, hα ▸ hF, rfl⟩

/-- **`oba_find` meets `findSpec`.** -/
theorem find_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm findFunc)
    (har : HasArity fi 2 1) : TFSpecAt P host a (findSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, x, e, ma, mt, B, n, α, rfl, -⟩
    simp [hps]
  · rintro s args ⟨-, x, e, ma, mt, B, n, α, rfl, hm, hO⟩ f vs₀
    rw [forCall_find, findFunc_body]
    refine (show TWP P host s (fr fi.module [x, e, 0]) (vals [] ++ expression [while_ _, lget 2])
      _ from ?_)
    wbegin
    exact t_while (Inv := FInv s fi.module x e α) (V := FV α) ⟨rfl, 0#32, rfl, by simp, by simp⟩
      (fun _ _ hI => find_body hm hO (fun i hF F =>
        bodyPostT_normal (by simp [hrs]) (find_post hm hO hF)) hI)

/-- **`OBASpec`, by tactics.** -/
theorem obaSpec_tactic : OBASpec := fun P host _ _ har =>
  ⟨fun hc => get_valid (P := P) (host := host) hc har,
   fun hc => find_valid (P := P) (host := host) hc har⟩

end Silmaril.WasmSpec.BTree.V2

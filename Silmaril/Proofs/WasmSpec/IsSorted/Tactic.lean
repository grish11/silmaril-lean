module

public import Silmaril.WasmSpec.IsSorted.Defs
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# `is_sorted`: the proof by tactics

Method `tactic`: symbolic execution with the rules and tactics of `Silmaril.Wasm.Logic.Words`
(`wrun`, `t_brIf`, `t_while`), the loop invariant `Inv` (the prefix of length `i` is sorted) and
the variant `n + 1 - i`; total correctness at every profile and for every host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.IsSorted

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem func_body : isSortedFunc.body = body := rfl

theorem forCall_eq (mi : ModuleInst) (p n : BitVec 32) :
    Frame.forCall mi [.i32 p, .i32 n] isSortedFunc.locals = fr mi [p, n, 0] := rfl

/-- The loop invariant: the store is `s₀`; local `2` is `i` with `1 ≤ i ≤ n + 1`, and the
prefix of length `i` of the array is sorted. -/
def Inv (s₀ : Store H) (mi : ModuleInst) (B : ByteArray) (p n : BitVec 32) (s : Store H)
    (f : Frame) : Prop :=
  s = s₀ ∧ ∃ i : BitVec 32, f = fr mi [p, n, i] ∧ 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat + 1 ∧
    SortedS ((words B p.toNat n.toNat).take i.toNat)

/-- The address of word `k`. -/
theorem addr_eq {p k : BitVec 32} {n : Nat} (hk : k.toNat < n) (hw : p.toNat + 4 * n < 2 ^ 32) :
    (p + k * 4#32).toNat = p.toNat + 4 * k.toNat := by
  bv_omega

theorem addr_pred_eq {p k : BitVec 32} {n : Nat} (h1 : 1 ≤ k.toNat) (hk : k.toNat < n)
    (hw : p.toNat + 4 * n < 2 ^ 32) :
    (p + (k - 1#32) * 4#32).toNat = p.toNat + 4 * (k.toNat - 1) := by
  bv_omega

/-- After the loop: `i32.ge_u i n` is the answer. -/
theorem after_loop {s₀ : Store H} {mi : ModuleInst} {B : ByteArray} {p n i : BitVec 32}
    {Q : Post H} (hQ : ∀ F, Q s₀ F (.normal [.i32 (answer (words B p.toNat n.toNat))]))
    (h : (n.toNat ≤ i.toNat ∧ SortedS ((words B p.toNat n.toNat).take i.toNat)) ∨
      (i.toNat < n.toNat ∧ ¬ SortedS (words B p.toNat n.toNat))) :
    TWP P host s₀ (fr mi [p, n, i]) (vals [] ++ expression [lget 2, lget 1, igeu]) Q := by
  wbegin
  wrun
  refine w_end (m := .total) ?_
  have hv : bool32 (decide (n.toNat ≤ i.toNat)) = answer (words B p.toNat n.toNat) := by
    rcases h with ⟨hle, hs⟩ | ⟨hlt, hs⟩
    · have hs' := sortedS_of_take hs (by simpa using hle)
      simp [answer, hs', hle, bool32]
    · simp [answer, hs, bool32, Nat.not_le.2 hlt]
  have hq := hQ (fr mi [p, n, i])
  rw [← hv] at hq
  simpa using hq

/-- The variant: `n + 1 - i`. -/
def V (n : BitVec 32) (_ : Store H) (f : Frame) : Nat := n.toNat + 1 - loc f 2

/-- The rest of an iteration with `i < n`: compare `a[i - 1]` and `a[i]`. -/
theorem loop_cmp {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p n i : BitVec 32} (hm : MemAt s mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hQ : ∀ F, Q s F (.normal [.i32 (answer (words B p.toNat n.toNat))]))
    (h1 : 1 ≤ i.toNat) (hs : SortedS ((words B p.toNat n.toNat).take i.toNat))
    (hc : i.toNat < n.toNat) :
    TWP P host s (fr mi [p, n, i]) (vals ([] : List Val).reverse ++ expression loopCmp)
      (whilePostT P host (Inv s mi B p n) (V n) (n.toNat + 1 - i.toNat)
        (expression [lget 2, lget 1, igeu]) Q) := by
  have hlen : i.toNat < (words B p.toNat n.toNat).length := by simpa using hc
  have e₁ : wd B (p + i * 4#32).toNat = (words B p.toNat n.toNat)[i.toNat] := by
    rw [addr_eq hc hw, getElem_words hc]
  have e₀ : wd B (p + (i - 1#32) * 4#32).toNat = (words B p.toNat n.toNat)[i.toNat - 1] := by
    rw [addr_pred_eq h1 hc hw, getElem_words (by omega)]
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hs' : (words B p.toNat n.toNat)[i.toNat - 1].toInt ≤
      (words B p.toNat n.toNat)[i.toNat].toInt →
      SortedS ((words B p.toNat n.toNat).take (i + 1#32).toNat) := fun hle => by
    rw [hi1]
    exact sortedS_take_succ hs h1 hlen hle
  have hv : V n s (fr mi [p, n, i + 1#32]) < n.toNat + 1 - i.toNat := by
    simp only [V, loc_fr (L := [p, n, i + 1#32]) (k := 2) (by simp), List.getD_cons_succ,
      List.getD_cons_zero]
    omega
  simp only [loopCmp]
  wbegin
  wrun
  rw [e₀, e₁]
  refine t_brIf (fun hc' => ?_) (fun hc' => ?_)
  · have hdesc : (words B p.toNat n.toNat)[i.toNat].toInt <
        (words B p.toNat n.toNat)[i.toNat - 1].toInt := by simpa using hc'
    exact whilePostT_exit (after_loop hQ (.inr ⟨hc, not_sortedS_of_desc h1 hlen hdesc⟩))
  · have hle : (words B p.toNat n.toNat)[i.toNat - 1].toInt ≤
        (words B p.toNat n.toNat)[i.toNat].toInt := by simpa using hc'
    wrun
    exact t_br (whilePostT_cont ⟨rfl, i + 1#32, rfl, by omega, by omega, hs' hle⟩ hv)

/-- **One iteration of the loop.** -/
theorem loop_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p n : BitVec 32} (hm : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hQ : ∀ F, Q s₀ F (.normal [.i32 (answer (words B p.toNat n.toNat))]))
    {s : Store H} {f : Frame} (hI : Inv s₀ mi B p n s f) :
    TWP P host s f (vals [] ++ expression loopBody)
      (whilePostT P host (Inv s₀ mi B p n) (V n) (V n s f) (expression [lget 2, lget 1, igeu]) Q) := by
  obtain ⟨rfl, i, rfl, h1, h2, hs⟩ := hI
  have hV : V n s (fr mi [p, n, i]) = n.toNat + 1 - i.toNat := by
    simp only [V, loc_fr (L := [p, n, i]) (k := 2) (by simp), List.getD_cons_succ,
      List.getD_cons_zero]
  rw [hV]
  simp only [loopBody, loopTest, List.cons_append, List.nil_append]
  wbegin
  wrun
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : n.toNat ≤ i.toNat := by simpa using hc
    exact whilePostT_exit (after_loop hQ (.inl ⟨hge, hs⟩))
  · have hlt : i.toNat < n.toNat := by simpa using hc
    exact loop_cmp hm hb hw hQ h1 hs hlt

/-- The body from the entry of the function. -/
theorem body_twp {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p n : BitVec 32} (hm : MemAt s mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hQ : ∀ F, Q s F (.normal [.i32 (answer (words B p.toNat n.toNat))])) :
    TWP P host s (fr mi [p, n, 0]) (vals [] ++ expression body) Q := by
  simp only [body]
  wbegin
  wrun
  refine t_while (Inv := Inv s mi B p n) (V := V n) ⟨rfl, 1#32, rfl, by simp, by simp,
    by simpa using sortedS_take_one _⟩ fun s' f hI => ?_
  have hI' := hI
  obtain ⟨rfl, -⟩ := hI'
  exact loop_body hm hb hw hQ hI

/-- **`is_sorted` meets its specification** (total correctness), at every profile and for
every host relation, for any function instance whose code is `isSortedFunc` and whose type
has two parameters and one result. -/
theorem isSorted_valid {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm isSortedFunc) (he : Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) :
    TFSpecAt P host a (isSortedSpec a fi) := by
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, p, n, ma, mt, B, rfl, -⟩
    simp [hps]
  · rintro s args ⟨-, p, n, ma, mt, B, rfl, hm, hb, hw⟩ f vs₀
    have hQ : ∀ F, bodyPostT P host rs.length f vs₀
        (callPost f vs₀ ((isSortedSpec a fi).post s [.i32 p, .i32 n])) s F
        (.normal [.i32 (answer (words B p.toNat n.toNat))]) := fun F =>
      bodyPostT_normal (by simp [hrs]) ⟨rfl, fun p' n' ma' mt' B' hargs hm' => by
        simp only [List.cons.injEq, and_true] at hargs
        obtain rfl := i32_inj hargs.1
        obtain rfl := i32_inj hargs.2
        obtain ⟨-, -, rfl⟩ := hm'.unique hm
        rfl⟩
    have h := body_twp (P := P) (host := host) hm hb hw hQ
    rw [forCall_eq, func_body]
    simpa [TWP] using h

/-- The instantiated store holds `is_sorted` as its only function, of type
`[i32, i32] → [i32]`. -/
theorem store₀_funcs : ∃ fi : FuncInst Nat, store₀.funcs = [fi] ∧
    fi.code = .wasm isSortedFunc ∧
    Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩ := by
  have hlen : store₀.funcs.length = 1 := rfl
  obtain ⟨fi, hf⟩ := List.length_eq_one_iff.mp hlen
  have hc : store₀.funcs.map FuncInst.code = [.wasm isSortedFunc] := rfl
  have ht : store₀.funcs.map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      [some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨fi, hf, hc, ht⟩

/-- **`Spec`, by tactics.** -/
theorem spec_tactic : Spec := fun P host _ _ _ _ hcode he hps hrs =>
  isSorted_valid (P := P) (host := host) hcode he hps hrs

/-- **`SpecStore`, by tactics**: the instantiated `is_sorted` meets its specification. -/
theorem specStore_tactic : SpecStore := by
  obtain ⟨fi, hf, hc, ht⟩ := store₀_funcs
  refine ⟨fi, by rw [hf]; rfl, fun P host => ?_⟩
  exact isSorted_valid hc (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? ht) rfl rfl

end Silmaril.WasmSpec.IsSorted

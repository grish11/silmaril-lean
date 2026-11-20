module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Words
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Sorted

/-!
# `sortedNCheck` meets its specification

`sortedNCheck_sat`: in every environment `ρ` and every profile, the instance of `sortedNCheck`
meets the n-ary reader specification for `sortedNL` (lists of words, non-decreasing in the
signed `i64` order) with the store invariant `StoreInv`. Loop invariant: the locals are
`[h, n, i, c, w, p]`, `i ≤ n`, the first `i` children are the atoms `ws`, `ws` is sorted and
every word of `ws` is at most `p` (vacuous while `i = 0`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Nary Silmaril.Wasm.Game.HandleAccept.Nary.Examples
  Silmaril.Wasm.Game.HandleAccept.Nary.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The body of `sortedNCheck`'s function. -/
def sortedNBody : List Instr := listHead ++ [.loop .empty (loopHead ++ elemSortedN ++ loopTail)]

theorem sortedN_shape : GShape (Verify.instOf sortedNCheck) sxFTs aFT
    [.i32, .i32, .i32, .i64, .i64] sortedNBody
    [some (.i32 0), some (.i32 0), some (.i32 0), some (.i64 0), some (.i64 0)] :=
  GShape.of_ok (by decide +kernel)

/-- The sorted prefix: `ws` is sorted and bounded by `p`. -/
def SortedUpTo (ws : List (BitVec 64)) (p : BitVec 64) : Prop :=
  ws.Pairwise (fun a b => a.sle b = true) ∧ ∀ x ∈ ws, x.sle p = true

theorem sle_refl' (w : BitVec 64) : w.sle w = true := by
  simp [BitVec.sle]

/-- One more word, at least the bound when there are words already. -/
theorem sortedUpTo_snoc {ws : List (BitVec 64)} {p w : BitVec 64} (h : SortedUpTo ws p)
    (hle : ws ≠ [] → p.sle w = true) : SortedUpTo (ws ++ [w]) w := by
  have hb : ∀ x ∈ ws, x.sle w = true := fun x hx =>
    sle_trans (h.2 x hx) (hle (List.ne_nil_of_mem hx))
  refine ⟨List.pairwise_append.2 ⟨h.1, List.pairwise_singleton _ _, fun a ha b hb' => ?_⟩,
    fun x hx => ?_⟩
  · rw [List.mem_singleton] at hb'
    subst hb'
    exact hb a ha
  · rcases List.mem_append.1 hx with hx | hx
    · exact hb x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact sle_refl' _

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))}

/-- The loop invariant, for `h` denoting `SExp.ofList cs` with `n` children. -/
def SortedNInv (s₀ : Store Nat) (h n : BitVec 32) (cs : List (SExp (BitVec 64)))
    (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ (i c : BitVec 32) (w p : BitVec 64) (ws : List (BitVec 64)),
    f = ⟨[some (.i32 h), some (.i32 n), some (.i32 i), some (.i32 c), some (.i64 w),
      some (.i64 p)], mi⟩ ∧
    i.toNat ≤ n.toNat ∧ cs.take i.toNat = ws.map .atom ∧ ws.length = i.toNat ∧ SortedUpTo ws p

/-- After the comparison: record the word, next index, loop. -/
theorem sortedN_tail {s : Store Nat} {mi : ModuleInst} {h n i c : BitVec 32} {w p : BitVec 64}
    {cs : List (SExp (BitVec 64))} {ws : List (BitVec 64)} {Q : Post Nat}
    (hi : i.toNat ≤ n.toNat) (hne : i ≠ n) (ht : cs.take i.toNat = ws.map .atom)
    (hws : ws.length = i.toNat) (hsort : SortedUpTo ws p) (hx : cs[i.toNat]? = some (.atom w))
    (hle : i ≠ 0 → p.sle w = true) :
    HWP P (gameHost (Verify.instOf sortedNCheck) (sexpISpec pairIx ρ sortedNL)) s
      ⟨[some (.i32 h), some (.i32 n), some (.i32 i), some (.i32 c), some (.i64 w),
        some (.i64 p)], mi⟩
      (vals [] ++ expression [.localGet ⟨4⟩, .localSet ⟨5⟩, .localGet ⟨2⟩, .intConst .i32 1,
        .intBinOp .i32 .add, .localSet ⟨2⟩, .br ⟨0⟩])
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ SortedNInv s h n cs mi s' f) Q) := by
  refine X.localGet (v := .i64 w) rfl ?_
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 i) rfl ?_
  refine X.i32Const ?_
  refine X.add32 ?_
  refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
  have hsucc := toNat_succ hi hne
  have hlt := lt_of_ne hi hne
  refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, i + 1, c, w, w, ws ++ [w], rfl, ?_, ?_, ?_, ?_⟩
  · rw [hsucc]
    omega
  · rw [hsucc]
    exact take_succ_atom ht hx
  · rw [hsucc, List.length_append, hws]
    rfl
  · refine sortedUpTo_snoc hsort fun hne' => hle fun h0 => hne' ?_
    subst h0
    exact List.eq_nil_of_length_eq_zero hws

theorem sortedN_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf sortedNCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = List.range (sxFTs.length + 1)) {h n i c : BitVec 32}
    {w p : BitVec 64} {cs : List (SExp (BitVec 64))} {ws : List (BitVec 64)} {Q : Post Nat}
    (hQ : Leaves Q s) (hcs : ρ h = some (SExp.ofList cs)) (hlen : cs.length = n.toNat)
    (hi : i.toNat ≤ n.toNat) (ht : cs.take i.toNat = ws.map .atom) (hws : ws.length = i.toNat)
    (hsort : SortedUpTo ws p) :
    HWP P (gameHost (Verify.instOf sortedNCheck) (sexpISpec pairIx ρ sortedNL)) s
      ⟨[some (.i32 h), some (.i32 n), some (.i32 i), some (.i32 c), some (.i64 w),
        some (.i64 p)], mi⟩
      (vals [] ++ expression (loopHead ++ elemSortedN ++ loopTail))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ SortedNInv s h n cs mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ SortedNInv s h n cs mi s' f)
  have hS := sortedN_shape
  simp only [loopHead, elemSortedN, loopTail, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 i) rfl ?_
  refine X.localGet (v := .i32 n) rfl ?_
  refine X.rel32 ?_
  refine X.if_ (fun heq => ?_) (fun hne => ?_)
  · obtain rfl := rel32_eq_ne_zero heq
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxAccept hS hs hm (fun t ht' => ?_) hL.label (X.return_ ((hL.label _).1 _))
    rw [hcs] at ht'
    cases ht'
    exact ⟨ws, eq_of_take hlen ht, hsort.1⟩
  · have hne' := rel32_eq_zero hne
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localGet (v := .i32 i) rfl ?_
    refine X.sxChild hS hs hm hL (fun c' cs' x hcs' hx hc' => ?_)
    obtain rfl : cs' = cs := SExp.ofList_injective (Option.some.inj (hcs'.symm.trans hcs))
    refine X.localSet (by simp [Idx.toNat]) ?_
    refine X.localGet (v := .i32 c') rfl ?_
    refine X.sxKind hS hs hm hL (fun k _ => ?_)
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun _ => ?_)
    refine X.localGet (v := .i32 c') rfl ?_
    refine X.sxWord hS hs hm hL (fun w' hw' => ?_)
    obtain rfl : x = .atom w' := Option.some.inj (hc'.symm.trans hw')
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.localGet (v := .i32 i) rfl ?_
    refine X.if_ (fun hb => ?_) (fun hb => ?_)
    · refine X.localGet (v := .i64 p) rfl ?_
      refine X.localGet (v := .i64 w') rfl ?_
      refine X.les64 (us := []) ?_
      refine X.eqz ?_
      refine X.if_ (fun _ => X.return_ ((hL.label.label _).1 _)) (fun hz => ?_)
      have hle : p.sle w' = true := by simpa [bool32] using hz
      exact X.blockEnd (sortedN_tail hi hne' ht hws hsort hx fun _ => hle)
    · exact sortedN_tail hi hne' ht hws hsort hx fun hb' => absurd hb hb'

/-- **`sortedNCheck` meets the n-ary reader specification for `sortedNL`** in every
environment and every profile. -/
theorem sortedNCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))) :
    GameSat P (Verify.instOf sortedNCheck) (StoreInv (Verify.instOf sortedNCheck))
      (sexpISpec pairIx ρ sortedNL) (topISpec _) :=
  gameSat_ofG sortedN_shape rfl fun fi s args Q ht _ hm hs hQ _ => by
    obtain ⟨h, rfl⟩ := args_aFT ht
    have hS := sortedN_shape
    simp only [sortedNBody, listHead, List.cons_append, List.nil_append]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxKind hS hs hm hQ (fun c _ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun _ => ?_)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxCount hS hs hm hQ (fun n cs hcs hlen => ?_)
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := SortedNInv s h n cs fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, i, c, w, p, ws, rfl, hi, ht, hws, hsort⟩ := hI
        exact sortedN_loop hs hm hQ hcs hlen hi ht hws hsort)
      ⟨rfl, 0, 0, 0, 0, [], rfl, by simp, by simp, rfl, .nil,
        fun _ hx => absurd hx List.not_mem_nil⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

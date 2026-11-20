module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Basic
public import Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Defs

/-!
# `wordsNCheck` meets its specification

`wordsNCheck_sat`: in every environment `ρ` and every profile, the instance of `wordsNCheck`
meets the n-ary reader specification for `wordsNL` (lists of words) with the store invariant
`StoreInv`. After `kind` and `count`, `h` denotes `SExp.ofList cs` with `n` children; loop
invariant: the locals are `[h, n, i, c]`, `i ≤ n` (unsigned) and the first `i` children are
the atoms `ws`.

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

/-! ## Index arithmetic -/

/-- The index does not wrap: it stays below the count. -/
theorem toNat_succ {i n : BitVec 32} (hi : i.toNat ≤ n.toNat) (hne : i ≠ n) :
    (i + 1).toNat = i.toNat + 1 := by
  have h1 : i.toNat ≠ n.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  have h2 := n.isLt
  have h3 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, h3]
  omega

theorem lt_of_ne {i n : BitVec 32} (hi : i.toNat ≤ n.toNat) (hne : i ≠ n) : i.toNat < n.toNat := by
  have h1 : i.toNat ≠ n.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  omega

/-- One more atom child. -/
theorem take_succ_atom {cs : List (SExp (BitVec 64))} {k : Nat} {ws : List (BitVec 64)}
    {w : BitVec 64} (ht : cs.take k = ws.map .atom) (hk : cs[k]? = some (.atom w)) :
    cs.take (k + 1) = (ws ++ [w]).map .atom := by
  rw [List.take_add_one, ht, hk]
  simp

/-- All the children are the atoms `ws`. -/
theorem eq_of_take {cs : List (SExp (BitVec 64))} {n : Nat} {ws : List (BitVec 64)}
    (hlen : cs.length = n) (ht : cs.take n = ws.map .atom) : SExp.ofList cs = SExp.ofAtoms ws := by
  rw [← hlen, List.take_length] at ht
  rw [ht]
  rfl

/-! ## The checker -/

/-- The body of `wordsNCheck`'s function. -/
def wordsNBody : List Instr := listHead ++ [.loop .empty (loopHead ++ loopTail)]

theorem wordsN_shape : GShape (Verify.instOf wordsNCheck) sxFTs aFT [.i32, .i32, .i32] wordsNBody
    [some (.i32 0), some (.i32 0), some (.i32 0)] :=
  GShape.of_ok (by decide +kernel)

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))}

/-- The loop invariant, for `h` denoting `SExp.ofList cs` with `n` children. -/
def WordsNInv (s₀ : Store Nat) (h n : BitVec 32) (cs : List (SExp (BitVec 64))) (mi : ModuleInst)
    (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ (i c : BitVec 32) (ws : List (BitVec 64)),
    f = ⟨[some (.i32 h), some (.i32 n), some (.i32 i), some (.i32 c)], mi⟩ ∧
    i.toNat ≤ n.toNat ∧ cs.take i.toNat = ws.map .atom

theorem wordsN_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf wordsNCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = List.range (sxFTs.length + 1)) {h n i c : BitVec 32}
    {cs : List (SExp (BitVec 64))} {ws : List (BitVec 64)} {Q : Post Nat}
    (hQ : Leaves Q s) (hcs : ρ h = some (SExp.ofList cs)) (hlen : cs.length = n.toNat)
    (hi : i.toNat ≤ n.toNat) (ht : cs.take i.toNat = ws.map .atom) :
    HWP P (gameHost (Verify.instOf wordsNCheck) (sexpISpec pairIx ρ wordsNL)) s
      ⟨[some (.i32 h), some (.i32 n), some (.i32 i), some (.i32 c)], mi⟩
      (vals [] ++ expression (loopHead ++ loopTail))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ WordsNInv s h n cs mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ WordsNInv s h n cs mi s' f)
  have hS := wordsN_shape
  simp only [loopHead, loopTail, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 i) rfl ?_
  refine X.localGet (v := .i32 n) rfl ?_
  refine X.rel32 ?_
  refine X.if_ (fun heq => ?_) (fun hne => ?_)
  · obtain rfl := rel32_eq_ne_zero heq
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxAccept hS hs hm (fun t ht' => ?_) hL.label (X.return_ ((hL.label _).1 _))
    rw [hcs] at ht'
    cases ht'
    exact ⟨ws, eq_of_take hlen ht⟩
  · have hne' := rel32_eq_zero hne
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localGet (v := .i32 i) rfl ?_
    refine X.sxChild hS hs hm hL (fun c' cs' x hcs' hx hc' => ?_)
    obtain rfl : cs' = cs := SExp.ofList_injective (Option.some.inj (hcs'.symm.trans hcs))
    refine X.localSet (by simp [Idx.toNat]) ?_
    refine X.localGet (v := .i32 c') rfl ?_
    refine X.sxKind hS hs hm hL (fun k hk => ?_)
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun hk0 => ?_)
    obtain ⟨w, hw⟩ : ∃ w, ρ c' = some (.atom w) := by
      rcases hk with ⟨-, hw⟩ | ⟨rfl, -⟩
      · exact hw
      · exact absurd hk0 (by decide)
    obtain rfl : x = .atom w := Option.some.inj (hc'.symm.trans hw)
    refine X.localGet (v := .i32 i) rfl ?_
    refine X.i32Const ?_
    refine X.add32 ?_
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    have hsucc := toNat_succ hi hne'
    have hlt := lt_of_ne hi hne'
    refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, i + 1, c', ws ++ [w], rfl, ?_, ?_⟩
    · rw [hsucc]
      omega
    · rw [hsucc]
      exact take_succ_atom ht hx

/-- **`wordsNCheck` meets the n-ary reader specification for `wordsNL`** in every environment
and every profile. -/
theorem wordsNCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))) :
    GameSat P (Verify.instOf wordsNCheck) (StoreInv (Verify.instOf wordsNCheck))
      (sexpISpec pairIx ρ wordsNL) (topISpec _) :=
  gameSat_ofG wordsN_shape rfl fun fi s args Q ht _ hm hs hQ _ => by
    obtain ⟨h, rfl⟩ := args_aFT ht
    have hS := wordsN_shape
    simp only [wordsNBody, listHead, List.cons_append, List.nil_append]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxKind hS hs hm hQ (fun c _ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun _ => ?_)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxCount hS hs hm hQ (fun n cs hcs hlen => ?_)
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := WordsNInv s h n cs fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, i, c, ws, rfl, hi, ht⟩ := hI
        exact wordsN_loop hs hm hQ hcs hlen hi ht)
      ⟨rfl, 0, 0, [], rfl, by simp, by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

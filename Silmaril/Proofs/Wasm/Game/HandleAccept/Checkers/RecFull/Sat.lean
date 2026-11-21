module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Proper
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.Calls
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Defs

/-!
# `recFullCheck` meets its specification

The exported function of `recFullCheck` calls itself, so its proof needs a specification for the
internal call. `rfSpec I ρ B`: called on `h` denoting a tree of size below `B` (`rfSize`, the
number of cons cells), the function leaves the store unchanged and, if it returns normally,
`h` denotes a recursively proper list.

* `rf_valid`: `rfSpec … B` is valid at the function's address for every `B`, by induction on
  `B`: inside the body, every recursive call is on an element of the spine of `h`, a strictly
  smaller tree, so the induction hypothesis (`FSpecValid` for `B`) gives the call rule
  (`X.callSpec`); the body is otherwise one loop with invariant `RFInv` (`cur` denotes a tree of
  size at most that of `h`'s, and if `cur` denotes a recursively proper list so does `h`);
* `recFullCheck_sat`: the export meets the cons reader specification for `recProperL` in every
  environment `ρ` and profile, from the same body lemma `rf_body` (the bound taken from the
  tree of the argument; an unresolved argument traps at its first `kind`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The number of cons cells of a tree. -/
def rfSize {α : Type} : SExp2 α → Nat
  | .cons x y => rfSize x + rfSize y + 1
  | _ => 0

/-- The instance. -/
noncomputable abbrev rfI : ScalarInstance := Verify.instOf recFullCheck

/-- The body of the function. -/
def rfBody : List Instr := [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty (rfHead ++ rfElem)]

theorem rf_shape : Shape rfI [.i32, .i32, .i32] rfBody
    [some (.i32 0), some (.i32 0), some (.i32 0)] :=
  Shape.of_okR (by decide +kernel)

/-- **The specification of the internal call** on arguments denoting trees of size below `B`. -/
def rfSpec (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (B : Nat) :
    FSpec Nat where
  pre s args := s.funcs = rfI.store.funcs ∧
    ∃ h, args = [.i32 h] ∧ ∃ t, ρ h = some t ∧ rfSize t < B
  post s args s' o := s' = s ∧ ∀ res, o = .normal res →
    res = [] ∧ ∀ h, args = [.i32 h] → Good ρ recProperL h

/-- The loop invariant. -/
def RFInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (B : Nat)
    (s₀ : Store Nat) (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ cur k e : BitVec 32,
    f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩ ∧
    (∀ t, ρ cur = some t → rfSize t < B + 1) ∧ (Good ρ recProperL cur → Good ρ recProperL h)

theorem i32_singleton_inj {a b : BitVec 32} (h : [Val.i32 a] = [Val.i32 b]) : a = b := by
  simp only [List.cons.injEq, and_true] at h
  cases h
  rfl

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

section Body

variable {s : Store Nat} (hs : s.funcs = rfI.store.funcs) {mi : ModuleInst}
  (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {B : Nat}
  (hB : FSpecValid P (gameHost rfI (consISpec consIx ρ recProperL)) 5 (rfSpec ρ B))
  {h : BitVec 32} {Q : Post Nat} (hQ : TrapsQ Q s) (hR : Good ρ recProperL h → RetQ Q s)

include hs hB in
/-- The recursive call on an element denoting a tree of size below `B`. -/
theorem R.self {f : Frame} (hmf : f.module.funcs = [0, 1, 2, 3, 4, 5]) {us : List Val}
    {is : List Instr} {Q' : Post Nat} (hQ' : TrapsQ Q' s) {e : BitVec 32} {x : SExp2 (BitVec 64)}
    (he : ρ e = some x) (hx : rfSize x < B)
    (hk : x ∈ recProperL →
      HWP P (gameHost rfI (consISpec consIx ρ recProperL)) s f (vals us ++ expression is) Q') :
    HWP P (gameHost rfI (consISpec consIx ρ recProperL)) s f
      (vals (us ++ [.i32 e]) ++ expression (.call ⟨5⟩ :: is)) Q' := by
  obtain ⟨fi, code, ps, rs, hf, -⟩ := rf_shape.fn
  refine X.callSpec (a := 5) (fi := fi) (by rw [hmf]; rfl) (by rw [hs]; exact hf) hB
    ⟨hs, e, rfl, x, he, hx⟩ ?_ ?_ ?_
  · rintro s' res ⟨rfl, hpost⟩
    obtain ⟨rfl, hg⟩ := hpost res rfl
    simpa using hk (hg e rfl x he)
  · rintro s' ⟨rfl, -⟩
    exact (hQ' f).1
  · rintro s' y ⟨rfl, -⟩
    exact (hQ' f).2 y

include hs hm hB hQ hR

/-- The loop body. -/
theorem rf_loop {cur k e : BitVec 32} (hc : ∀ t, ρ cur = some t → rfSize t < B + 1)
    (hg : Good ρ recProperL cur → Good ρ recProperL h) :
    HWP P (gameHost rfI (consISpec consIx ρ recProperL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩
      (vals [] ++ expression (rfHead ++ rfElem))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f) Q) := by
  have hL : TrapsQ (loopPost 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f) Q) s :=
    hQ.loop
  have hS := rf_shape
  simp only [rfHead, rfElem, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 cur) rfl ?_
  refine R.kind hS hs hm hL (fun k' hk => ?_)
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 k') rfl ?_
  refine X.eqz ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · -- nil: accept `h` and return
    have hk0 : k' = 0 := by simpa using bool32_ne_zero h0
    have hnil : ρ cur = some .nil := by
      rcases hk with ⟨-, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn
      · exact absurd hk0 (by decide)
      · exact absurd hk0 (by decide)
    have hgh : Good ρ recProperL h := hg fun t ht => by
      rw [hnil] at ht
      cases ht
      exact .nil
    refine X.localGet (v := .i32 h) rfl ?_
    refine R.accept hS hs hm hgh hL.label ?_
    exact X.return_ (((hR hgh).loop).label _)
  · refine X.localGet (v := .i32 k') rfl ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => Wp.unreachable (m := .part) (us := []) (hL.label _).1) (fun h2 => ?_)
    -- a cons cell: the element
    refine X.localGet (v := .i32 cur) rfl ?_
    refine R.car hS hs hm hL (fun e' x y hcur he' => ?_)
    have hsz := hc _ hcur
    simp only [rfSize] at hsz
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    -- the advance, once the element is known to be proper
    have adv : SExp2.IsProper x →
        HWP P (gameHost rfI (consISpec consIx ρ recProperL)) s
          ⟨[some (.i32 h), some (.i32 cur), some (.i32 k'), some (.i32 e')], mi⟩
          (vals [] ++ expression [.localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩])
          (loopPost 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f) Q) := by
      intro hx
      refine X.localGet (v := .i32 cur) rfl ?_
      refine R.cdr (us := []) hS hs hm hL (fun c' x' y' hcur' hc' => ?_)
      refine X.localSet (by simp [Idx.toNat]) ?_
      rw [hcur] at hcur'
      obtain ⟨rfl, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
      refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, c', k', e', rfl,
        fun t ht => ?_, fun hg' => hg fun t ht => ?_⟩
      · rw [hc'] at ht
        cases ht
        omega
      · rw [hcur] at ht
        cases ht
        rcases hx with hx | hx
        · exact .cons hx (hg' _ hc')
        · exact .cons hx (hg' _ hc')
    refine X.localGet (v := .i32 e') rfl ?_
    refine R.kind hS hs hm hL (fun k₂ hk₂ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun h1 => ?_) (fun h1 => ?_)
    · -- not an atom: check it recursively
      refine X.localGet (v := .i32 e') rfl ?_
      refine R.self hs hB hm (us := []) hL.label he' (by omega) (fun hxp => ?_)
      exact X.blockEnd (adv (.inr hxp))
    · -- an atom
      have hk1 : k₂ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
      obtain ⟨w, hw⟩ : ∃ w, ρ e' = some (.atom w) := by
        rcases hk₂ with ⟨rfl, -⟩ | ⟨-, hw⟩ | ⟨rfl, -⟩
        · exact absurd hk1 (by decide)
        · exact hw
        · exact absurd hk1 (by decide)
      obtain rfl : x = .atom w := Option.some.inj (he'.symm.trans hw)
      exact adv (.inl (.atom w))

/-- The body of the function, from the frame of a call on `h`. -/
theorem rf_body (hh : ∀ t, ρ h = some t → rfSize t < B + 1) :
    HWP P (gameHost rfI (consISpec consIx ρ recProperL)) s
      ⟨some (.i32 h) :: [some (.i32 0), some (.i32 0), some (.i32 0)], mi⟩
      (vals [] ++ expression rfBody) Q := by
  refine X.localGet (v := .i32 h) rfl ?_
  refine X.localSet (by simp [Idx.toNat]) ?_
  exact X.loop (Inv := RFInv ρ B s h mi)
    (fun s' f hI => by
      obtain ⟨rfl, cur, k, e, rfl, hc, hg⟩ := hI
      exact rf_loop hs hm hB hQ hR hc hg) ⟨rfl, h, 0, 0, rfl, hh, id⟩

end Body

/-- **The internal call meets `rfSpec … B`** for every bound `B`. -/
theorem rf_valid (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    ∀ B, FSpecValid P (gameHost rfI (consISpec consIx ρ recProperL)) 5 (rfSpec ρ B)
  | 0 => fun _ _ _ hpre => by
    obtain ⟨-, _, -, _, -, ht⟩ := hpre
    exact absurd ht (Nat.not_lt_zero _)
  | B + 1 => by
    have ih := rf_valid ρ B
    obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := rf_shape.fn
    intro n
    cases n with
    | zero => exact fun _ _ _ _ _ _ _ => trivial
    | succ n =>
      refine FSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
        (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
      · obtain ⟨-, h, rfl, -⟩ := hpre
        simp [hps]
      · obtain ⟨hs, h, rfl, t, ht, hlt⟩ := hpre
        have hfr : Frame.forCall fi.module [.i32 h] code.locals =
            ⟨some (.i32 h) :: [some (.i32 0), some (.i32 0), some (.i32 0)], fi.module⟩ := by
          unfold Frame.forCall
          rw [hloc, hD]
          rfl
        rw [hfr, hbod]
        refine rf_body hs hm ih (fun F => ⟨?_, fun a => ?_⟩) (fun hg F => ?_)
          (fun t' ht' => by rw [ht] at ht'; cases ht'; exact hlt) n
        · exact ⟨rfl, .inr (.inl ⟨rfl, rfl, fun _ h => by cases h⟩)⟩
        · exact ⟨rfl, .inr (.inr ⟨a, rfl, rfl, fun _ h => by cases h⟩)⟩
        · refine ⟨[], [], by simp, by simp [hrs], rfl, .inl ⟨[], by simp, rfl, fun res hres => ?_⟩⟩
          cases hres
          exact ⟨rfl, fun h' hh' => by obtain rfl := i32_singleton_inj hh'; exact hg⟩

/-- **`recFullCheck` meets the cons reader specification for `recProperL`** in every
environment and every profile. -/
theorem recFullCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P rfI (StoreInv rfI) (consISpec consIx ρ recProperL) (topISpec _) :=
  gameSat_of rf_shape fun fi s h Q _ hm hs hQ => by
    refine rf_body (B := match ρ h with | some t => rfSize t | none => 0) hs hm
      (rf_valid ρ _) (fun F => ⟨(hQ F).2.1, (hQ F).2.2⟩) (fun _ F => (hQ F).1 [])
      (fun t ht => by simp only [ht]; omega)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull

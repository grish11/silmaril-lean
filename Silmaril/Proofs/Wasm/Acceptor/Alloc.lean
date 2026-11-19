module

public import Silmaril.Wasm.Acceptor.Alloc.Defs
public import Silmaril.Wasm.Examples.LRAT.Thms
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

@[expose] public section

/-!
# The acceptor kit's `cabi_realloc`: proofs

* `realloc_hwp`: in any store whose global `g` (through the module instance, at address `ga`)
  is the `i32` heap pointer `top ≤ N`, every run of the body of `cabi_realloc(old, osz, al, nsz)`
  returns one value `r` and only sets the global at `ga`, to some `t'`, as `ReallocOk N` says.
  It never traps. Every profile and host relation.
* `realloc_sound`: the same for every returning run of `$invoke` of a function instance whose
  code is `reallocFunc ty g N` (any type index, any address).
* `BumpSpec.bumpAlloc`: a `BumpSpec` and the size and write facts of the ABI memory give
  `ListLift.BumpAlloc` (the allocator never touches memory: `setGlobal` keeps every memory).

A Silmaril addition; the body proof is the one of the LRAT and Farkas acceptors, with the
global index and the memory size as parameters.
-/

namespace Silmaril.Proofs.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Acceptor (reallocBody reallocLocals reallocFunc alignUp ReallocOk BumpSpec)
open Silmaril.Wasm.Component.Reference.ListLift (BumpAlloc memBytesOf ReallocRun)

/-- Normalise literal frames. -/
macro "anorm" : tactic => `(tactic| try simp only [List.getD_cons_succ, List.getD_cons_zero,
  List.set_cons_succ, List.set_cons_zero])

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {s : Store H} {mi : ModuleInst} {L : List (BitVec 32)} {rs : List Val} {rest : List Admin}
  {Q : Post H} {gt : CGlobalType} {top : BitVec 32} {gi : GlobalInst} {g ga N : Nat}

theorem global?_g (hg : g < 2 ^ 32) (hmi : mi.globals[g]? = some ga)
    (hs : s.globals[ga]? = some gi) :
    s.global? (fr mi L) ⟨⟨g % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ = some (ga, gi) := by
  have e : g % 4294967296 = g := Nat.mod_eq_of_lt hg
  simp [Store.global?, fr, Idx.toNat, e, hmi, hs]

/-- `global.get g` of an `i32` global. -/
theorem w_ggetA {v : BitVec 32} (hg : g < 2 ^ 32) (hmi : mi.globals[g]? = some ga)
    (hs : s.globals[ga]? = some ⟨gt, Val.i32 v⟩)
    (h : HWP P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals rs.reverse ++ .plain (gget g) :: rest) Q := by
  rw [vals_rev_cons, List.append_assoc] at h
  exact Wp.globalGet (m := .part) (global?_g hg hmi hs) (by simpa using h)

/-- `global.set g`. -/
theorem w_gsetA (hg : g < 2 ^ 32) (hmi : mi.globals[g]? = some ga) (hs : s.globals[ga]? = some gi)
    {v : BitVec 32}
    (h : HWP P host (s.setGlobal ga (Val.i32 v)) (fr mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (gset g) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 v).toAdmin] =
    vals (rs.reverse ++ [Val.i32 v]) by simp]
  exact Wp.globalSet (m := .part) (global?_g hg hmi hs) h

/-- The postcondition of the body: one result and only the heap pointer changed. -/
def reallocPost (N ga : Nat) (s : Store H) (top al nsz : BitVec 32) : Store H → Outcome → Prop :=
  fun s' o => ∃ r t' : BitVec 32, o = .normal [Val.i32 r] ∧ s' = s.setGlobal ga (Val.i32 t') ∧
    ReallocOk N top al nsz r t'

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- **`cabi_realloc`, every run of the body.** -/
theorem realloc_hwp (hN : N < 2 ^ 32) (hg : g < 2 ^ 32) (hmi : mi.globals[g]? = some ga)
    (hs : s.globals[ga]? = some ⟨gt, Val.i32 top⟩) (htop : top.toNat ≤ N)
    (old osz al nsz : BitVec 32) :
    HWP P host s (fr mi [old, osz, al, nsz, 0, 0])
      (vals ([] : List Val).reverse ++ expression (reallocBody g N) ++ [])
      (bodyPost 1 (reallocPost N ga s top al nsz)) := by
  simp only [reallocBody, expression, List.map_cons, List.map_nil, List.cons_append,
    List.append_assoc]
  refine w_ggetA hg hmi hs ?_
  repeat (wstep; anorm)
  refine w_ggetA hg hmi hs ?_
  repeat (wstep; anorm)
  rw [b32_and, b32_and]
  generalize hp : (top + (al - BitVec.ofNat 32 1)) &&& (BitVec.ofNat 32 0 - al) = p
  have hpa : p = alignUp top al := by rw [← hp]; rfl
  have hNn : (BitVec.ofNat 32 N).toNat = N := toNat_ofNat_lt hN
  by_cases hfit : (top.toNat ≤ p.toNat ∧ p.toNat ≤ (BitVec.ofNat 32 N).toNat) ∧
      nsz.toNat ≤ (BitVec.ofNat 32 N - p).toNat
  · refine w_if (fun _ => ?_) (fun hc => absurd hfit (b32_eq_zero.1 hc))
    simp only [expression, List.map_cons, List.map_nil]
    wstep; anorm
    wstep; anorm
    wstep
    refine w_gsetA hg hmi hs ?_
    refine w_armEnd ?_
    wstep; anorm
    wstep
    refine w_if (fun hc => absurd hfit (b32_eq_zero.1 (b32_ne_zero.1 hc))) (fun _ => ?_)
    wstep; anorm
    refine w_end ⟨rfl, p, p + nsz, rfl, rfl, ?_⟩
    rw [hNn] at hfit
    obtain ⟨⟨h1, h2⟩, h3⟩ := hfit
    have h3' : nsz.toNat ≤ N - p.toNat := by
      have : (BitVec.ofNat 32 N - p).toNat = N - p.toNat := by
        rw [BitVec.toNat_sub, hNn]
        have := p.isLt
        omega
      omega
    have hsum : (p + nsz).toNat = p.toNat + nsz.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega, .inl ⟨hpa, h1, hsum.symm⟩⟩
  · refine w_if (fun hc => absurd (b32_ne_zero.1 hc) hfit) (fun _ => ?_)
    wstep; anorm
    wstep
    refine w_if (fun _ => ?_) (fun hc => absurd (b32_eq_zero.2 hfit) (b32_eq_zero.1 hc))
    simp only [expression, List.map_cons, List.map_nil]
    wstep
    refine w_gsetA hg hmi hs ?_
    wstep
    refine w_lset (by simp) (by decide) ?_
    anorm
    refine w_armEnd ?_
    wstep; anorm
    refine w_end ⟨rfl, BitVec.ofNat 32 N, BitVec.ofNat 32 N, rfl, rfl, ?_⟩
    exact ⟨by rw [hNn]; exact htop, by rw [hNn], .inr ⟨hNn, hNn⟩⟩

/-- The specification of `cabi_realloc` at address `a`. -/
def reallocSpec (N a ga : Nat) (fi : FuncInst H) (old osz al nsz top : BitVec 32) : FSpec H where
  pre s args := args = [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz] ∧
    s.funcs[a]? = some fi ∧ ∃ gt, s.globals[ga]? = some ⟨gt, Val.i32 top⟩
  post s _ s' o := reallocPost N ga s top al nsz s' o

/-- **`cabi_realloc`, every returning run**, for a function instance with the code of
`reallocFunc ty g N`. -/
theorem realloc_sound {s : Store H} {a : Nat} {fi : FuncInst H} {ty : TypeIdx}
    {ps rs : Ty (.list .val)} (hN : N < 2 ^ 32) (hg : g < 2 ^ 32)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (reallocFunc ty g N))
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 4) (hrs : rs.length = 1)
    (hmi : fi.module.globals[g]? = some ga) (hgl : s.globals[ga]? = some ⟨gt, Val.i32 top⟩)
    (htop : top.toNat ≤ N)
    {old osz al nsz : BitVec 32} {s' : Store H} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s a [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal ga (Val.i32 t') ∧
      ReallocOk N top al nsz r t' := by
  have hS : FSpecValid P host a (reallocSpec N a ga fi old osz al nsz top) := by
    refine FSpecValid.of_body_hwp (fun s _ hpre => hpre.2.1) hcode he
      (fun _ _ hpre => by rw [hpre.1, hps]; rfl) fun s args hpre => ?_
    obtain ⟨rfl, -, gt', hg'⟩ := hpre
    rw [hrs, ← code_eq]
    exact realloc_hwp hN hg hmi hg' htop old osz al nsz
  obtain ⟨r, t', ho, hs', hok⟩ := hS.invoke_vals ⟨rfl, hfi, gt, hgl⟩ hrun
  cases ho
  exact ⟨r, t', rfl, hs', hok⟩

/-! ## The bump allocator -/

theorem memBytesOf_setGlobal (s : Store Nat) (a ma : Nat) (v : Val) :
    memBytesOf (s.setGlobal a v) ma = memBytesOf s ma := rfl

/-- **A `BumpSpec` is a `BumpAlloc`** for any memory whose size and writes the invariant
controls. -/
theorem BumpSpec.bumpAlloc {P : Profile} {ra ga ma N : Nat} {Inv : Store Nat → Nat → Prop}
    (hS : BumpSpec P ra ga N Inv) (size : ∀ {s t}, Inv s t → (memBytesOf s ma).size = N)
    (write : ∀ {s t p bs s'}, Inv s t →
      Silmaril.Wasm.SingleThreaded.memWrite? s ma p bs = some s' → Inv s' t) :
    BumpAlloc P ra ma N Inv where
  small := hS.small
  size := size
  write := write
  realloc := by
    rintro s t al n q s' hI ⟨f', hs, hq⟩
    have ht := hS.le hI
    have hN := hS.small
    have htn : (BitVec.ofNat 32 t).toNat = t := toNat_ofNat_lt (by omega)
    obtain ⟨r, t', hres, rfl, hok⟩ := hS.run hI hs
    simp only [List.cons.injEq, and_true] at hres
    have hr : BitVec.ofNat 32 q = r := by
      injection hres with h₁
      injection h₁
    have hqr : q = r.toNat := by rw [← hr, toNat_ofNat_lt hq]
    obtain ⟨hlo, hhi, hcase⟩ := hok
    refine ⟨t'.toNat, hS.set hI hlo hhi, memBytesOf_setGlobal _ _ _ _, ?_, ?_⟩
    · rw [htn] at hcase
      rcases hcase with ⟨-, h₁, -⟩ | ⟨h₁, -⟩ <;> omega
    · intro hb
      have hn : (BitVec.ofNat 32 n).toNat = n := toNat_ofNat_lt (by omega)
      rw [hn] at hcase
      rcases hcase with ⟨-, -, h₁⟩ | ⟨h₁, h₂⟩ <;> omega

end Silmaril.Proofs.Wasm.Acceptor

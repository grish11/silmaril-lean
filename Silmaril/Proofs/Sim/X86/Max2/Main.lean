import Silmaril.Proofs.Sim.X86.Max2.Funcs

/-!
# The `max2` problem: the wrapper, and the whole module

* `max2_vc`: the SysV wrapper `max2(rdi, rsi)` (sets `rdi`, `rsi`, pushes the return address
  `-4096` at `rsp = 0x10fff8`, calls `f_400005`, checks `rip = -4096`, returns `rax`) returns
  the `@ensures` value;
* `ctxBelow_valid`: every specification of `specOf` is valid (by induction along the
  addresses: each function from the specifications of its callees);
* **`max2_valid`**: the export `max2` meets `sMax2` at every profile and host relation.

Not a `module` (see `Silmaril.Proofs.Sim.X86.Max2.Funcs`).
-/

namespace Silmaril.Sim.X86.Max2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)

variable {H : Type} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {fis : Nat → FuncInst H}


theorem ld64_storeLE {B : ByteArray} {a : Nat} (v : BitVec 64) (h : a + 8 ≤ B.size) :
    ld64 (storeLE B a 8 v.toNat) a = v := by
  have h1 := load_storeLE_same (n := 8) (B := B) (a := a) v h
  rw [load_ite, size_storeLE (n := 8) v.toNat h] at h1
  simp only [h, ↓reduceIte] at h1
  exact Option.some.inj h1

theorem ld64_storeLE_nat {B : ByteArray} {a v : Nat} (hv : v < 2 ^ 64) (h : a + 8 ≤ B.size) :
    ld64 (storeLE B a 8 v) a = BitVec.ofNat 64 v := by
  have := ld64_storeLE (BitVec.ofNat 64 v) h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem max2_vc (hnd : mi.globals.Nodup) (hf : mi.funcs = List.range 29) (s : Store H)
    (args : List Val) (hpre : (sMax2 mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 28) noInv 0 max2M.funcs[26].body
      (fnPost 1 ((sMax2 mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[26].locals) [] := by
  obtain ⟨hG, x, y, rfl⟩ := hpre
  have hma := good_ma hG
  have hsz := hG.size
  have c27 := callVC_at (Γ := ctxBelow mi ma mt fis 28) (m := mi) (x := ⟨27⟩) (a := 27)
    (by rw [hf]; rfl) rfl
  wat_vc_calls [↓vc_call 28 4, ↓vc_call 28 20, ↓vc_call 28 21, ↓c27,
    max2M, fnPost, sMax2, sSet, sGet, sStore64, sProg, procSpec, pureSpec, a32, a64,
    ctxBelow_specs, specOf, hf, hG, InWin, good_setR hnd, R_set_ne hnd, R_set_self',
    good_isSome hG, memB_setMem, hma, setGlobalIdx_mems, good_setMem, size_storeLE,
    ld64_storeLE_nat (v := 18446744073709547520) (by decide) (show 65528 + 8 ≤ (memB s ma).size by omega)]
  all_goals (repeat (first | apply good_setR hnd (by omega) | refine good_setMem _ ?_ ?_ | exact hG |
    (rw [size_storeLE _ (by omega)]; omega)))

/-- The arguments a precondition of the table admits have the arity of the table. -/
theorem specOf_len {a np : Nat} {S : FSpec H} (h : specOf mi ma mt fis a = some (np, S))
    {s : Store H} {args : List Val} (hp : S.pre s args) : args.length = np := by
  unfold specOf at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    simp only [sOff, sLoad64, sStore64, sRget, sRset, sFget, sFset, sFset6, sMask, sSbit, sParity,
      sFres, sRd, sWr, sCond, sAlu, sPop, sGet, sSet, sNext, sMovRR, sAluRR, sRet, sCmovRR, sProg,
      sMax2, pureSpec, procSpec, fnSpec] at hp <;>
    first
    | (obtain ⟨-, rfl⟩ := hp; rfl)
    | (obtain ⟨-, rfl, -⟩ := hp; rfl)
    | (obtain ⟨-, _, rfl⟩ := hp; rfl)
    | (obtain ⟨-, _, rfl, -⟩ := hp; rfl)
    | (obtain ⟨-, _, _, rfl⟩ := hp; rfl)
    | (obtain ⟨-, _, _, rfl, -⟩ := hp; rfl)
    | (obtain ⟨-, _, _, _, _, rfl⟩ := hp; rfl)
    | (obtain ⟨-, _, _, _, _, _, _, rfl⟩ := hp; rfl)

/-- Every precondition of the table includes `Good`. -/
theorem specOf_good {a np : Nat} {S : FSpec H} (h : specOf mi ma mt fis a = some (np, S))
    {s : Store H} {args : List Val} (hp : S.pre s args) : Good mi ma mt fis s := by
  unfold specOf at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> exact hp.1

theorem specOf_addr {a np : Nat} {S : FSpec H} (h : specOf mi ma mt fis a = some (np, S)) :
    2 ≤ a ∧ a < 29 := by
  unfold specOf at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

variable {P : Profile} {host : HostSemantics H}

/-- One function of the table from its verification condition and the validity of its callees'
specifications. -/
theorem fn_valid (hI : Inst mi ma mt fis) {n np : Nat} {S : FSpec H} {c : Func}
    (hS : specOf mi ma mt fis n = some (np, S)) (hc : max2M.funcs[n - 2]? = some c)
    (hΓ : (ctxBelow mi ma mt fis n).Valid P host) (inv : List Val → Store H → Invs H)
    (hvc : ∀ s args, S.pre s args → wpc (Γ := ctxBelow mi ma mt fis n) (inv args s) 0 c.body
      (fnPost (nres n) (S.post s args)) s (Frame.forCall mi args c.locals) []) :
    FSpecValid P host n S := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := hI.type n np S hS
  have ha := specOf_addr hS
  refine FSpecValid.of_wpc_fn hΓ inv (fun s args hp => (specOf_good hS hp).funcs n ha.2)
    (hI.code n c ha.1 hc) he (fun s args hp => (specOf_len hS hp).trans hps.symm)
    fun s args hp => ?_
  rw [hrs, hI.module n]
  exact hvc s args hp

/-- **All specifications of the table are valid**, by induction along the addresses. -/
theorem ctxBelow_valid (hI : Inst mi ma mt fis) : ∀ n, (ctxBelow mi ma mt fis n).Valid P host
  | 0 => fun a _ _ h => by
    change (if a < 0 then specOf mi ma mt fis a else none) = _ at h
    simp only [Nat.not_lt_zero, ↓reduceIte, reduceCtorEq] at h
  | n + 1 => by
    have ih := ctxBelow_valid hI n
    intro a np S h
    change (if a < n + 1 then specOf mi ma mt fis a else none) = some (np, S) at h
    by_cases han : a < n
    · refine ih a np S ?_
      change (if a < n then specOf mi ma mt fis a else none) = some (np, S)
      simp only [han, show a < n + 1 by omega, ↓reduceIte] at h ⊢
      exact h
    · have ha : a < n + 1 := by
        by_contra ha
        simp only [ha, ↓reduceIte, reduceCtorEq] at h
      have hn : a = n := by omega
      subst hn
      have hS : specOf mi ma mt fis a = some (np, S) := by simpa only [ha, ↓reduceIte] using h
      refine ⟨?_, fun s args hp => by rw [(specOf_good hS hp).funcs a (specOf_addr hS).2]; rfl⟩
      have hf := hI.funcs
      have hnd := hI.globals
      have hm := hI.mems
      unfold specOf at hS
      split at hS <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hS <;>
        obtain ⟨rfl, rfl⟩ := hS
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => off_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => load64_vc hm hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => store64_vc hm hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => rget_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => rset_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => fget_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => fset_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => fset6_vc hnd s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => mask_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => sbit_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => parity_vc s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => fres_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => rd_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => wr_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => cond_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => alu_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => pop_vc hnd hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => get_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => set_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => next_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => mov_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => aluRR_vc hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => ret_vc hnd hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => cmov_vc hf s args hp
      · exact fn_valid hI rfl rfl ih
          (fun _ s₀ _ s' f' a => s' = s₀ ∧ a = [] ∧
            f' = { locals := [some (Val.i32 0), some (Val.i32 0)], module := mi })
          fun s args hp => prog_vc hnd hf s args hp
      · exact fn_valid hI rfl rfl ih (fun _ _ => noInv) fun s args hp => max2_vc hnd hf s args hp

/-- **The generated x86 problem `max2` is solved**: in every instance of `max2M` laid out as
`Inst` (functions at addresses `0‥28`, distinct globals, memory `0` with a page), the exported
`max2(rdi, rsi)` returns `ite (bvsgt rsi rdi) rsi rdi` from every store satisfying `Good`, at
every profile and for every host relation (partial correctness: every run that stops returns
that value; none traps or gets stuck). -/
theorem max2_valid (hI : Inst mi ma mt fis) : FSpecValid P host 28 (sMax2 mi ma mt fis) :=
  (ctxBelow_valid hI 29 28 2 _ rfl).1

end Silmaril.Sim.X86.Max2

/-- info: 'Silmaril.Sim.X86.Max2.max2_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.X86.Max2.max2_valid

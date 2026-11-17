module

public import Silmaril.Proofs.Wasm.Examples.SatAccept.Nested
public import Silmaril.Proofs.Wasm.Examples.SatAccept.Instance

/-!
# The SAT acceptor: returning runs and the instance

Every run of `$invoke` of one of the three functions that returns values meets the function's
specification (`FnSpec.sound`, `FSpecValid.invoke_vals`): `realloc_returns`, `stream_returns`,
`nested_returns`. `isSpecInstance`: the instance of `prog` and its three function exports.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (satStream satNested)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}

theorem realloc_returns {o os al n t : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hg : globalVal s fi.module 0 = some (.i32 t))
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 o, .i32 os, .i32 al, .i32 n]) ⟨s', f', vals res⟩) :
    res = [.i32 (reallocRes t al n).1] ∧
      s' = setGlobalIdx s fi.module 0 (.i32 (reallocRes t al n).2) ∧
      ReallocOk t n (reallocRes t al n).1 (reallocRes t al n).2 := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) realloc_vc hc he
    (fun _ => by simp [reallocSpec, hps]) (by simpa [reallocSpec] using hrs) (o, os, al, n, t)
  obtain ⟨res', hres, hpost⟩ := FSpecValid.invoke_vals hv ⟨hfi, rfl, hg⟩ hs
  cases hres
  exact ⟨hpost.1, hpost.2, reallocRes_ok t al n⟩

theorem stream_returns {pp pl mp ml : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[1]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hsz : B.size = memBytes) (hP : pp.toNat + 4 * pl.toNat ≤ B.size)
    (hM : mp.toNat + 4 * ml.toNat ≤ B.size) (hg : (globalVal s fi.module 0).isSome)
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 pp, .i32 pl, .i32 mp, .i32 ml]) ⟨s', f', vals res⟩) :
    s' = setGlobalIdx s fi.module 0 (.i32 (BitVec.ofNat 32 heapBase)) ∧
      res = [.i32 (if satStream (wordsAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
        then 1 else 0)] := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) stream_vc hc he
    (fun _ => by simp [streamSpec, hps]) (by simpa [streamSpec] using hrs) (pp, pl, mp, ml)
  obtain ⟨res', hres, hpost⟩ :=
    FSpecValid.invoke_vals hv ⟨hfi, rfl, ⟨ma, mt, B, hmem, hsz, hP, hM⟩, hg⟩ hs
  cases hres
  exact ⟨hpost.1, hpost.2 ma mt B hmem⟩

theorem nested_returns {pp pl mp ml : BitVec 32} (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[2]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hsz : B.size = memBytes) (hN : NestedIn B pp.toNat pl.toNat)
    (hM : mp.toNat + 4 * ml.toNat ≤ B.size) (hg : (globalVal s fi.module 0).isSome)
    {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 pp, .i32 pl, .i32 mp, .i32 ml]) ⟨s', f', vals res⟩) :
    s' = setGlobalIdx s fi.module 0 (.i32 (BitVec.ofNat 32 heapBase)) ∧
      res = [.i32 (if satNested (nestedAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
        then 1 else 0)] := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) nested_vc hc he
    (fun _ => by simp [nestedSpec, hps]) (by simpa [nestedSpec] using hrs) (pp, pl, mp, ml)
  obtain ⟨res', hres, hpost⟩ :=
    FSpecValid.invoke_vals hv ⟨hfi, rfl, ⟨ma, mt, B, hmem, hsz, hN, hM⟩, hg⟩ hs
  cases hres
  exact ⟨hpost.1, hpost.2 ma mt B hmem⟩

/-! ## The instance -/

set_option maxRecDepth 100000 in
theorem validate_eq : validate? prog = some mt0 := by
  obtain ⟨mt, h⟩ := Option.isSome_iff_exists.1 t_valid
  simp [mt0, specMT, h]

set_option maxRecDepth 100000 in
theorem prepare_eq : prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0) = some prep := by
  obtain ⟨x, h⟩ := Option.isSome_iff_exists.1 t_prep
  simp [prep, specPrep, h]

theorem exists_fis : ∃ f₀ f₁ f₂ : FuncInst Nat, prep.1.store.funcs = [f₀, f₁, f₂] ∧
    FnType.ofDefType? f₀.type = some fnType4 ∧ FnType.ofDefType? f₁.type = some fnType4 ∧
    FnType.ofDefType? f₂.type = some fnType4 := by
  obtain ⟨f₀, f₁, f₂, h⟩ := List.length_eq_three.1 t_nf
  have h2 := t_ty
  rw [h] at h2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
  exact ⟨f₀, f₁, f₂, h, h2.1, h2.2.1, h2.2.2⟩

set_option maxRecDepth 100000 in
theorem isSpecInstance : IsSpecInstance prog mt0 inst prep.1 where
  valid := validate_eq
  funcImports := by rw [t_imports]; simp
  importTypes := by rw [t_imports]; exact .nil
  prepared := ⟨prep.1, prep.2, prepare_eq, by rw [t_start]; rfl, rfl, t_addrs⟩
  exportTypes := by
    obtain ⟨f₀, f₁, f₂, hfuncs, h₀, h₁, h₂⟩ := exists_fis
    refine .cons ⟨f₀, ?_, h₀⟩ (.cons ⟨f₁, ?_, h₁⟩ (.cons ⟨f₂, ?_, h₂⟩ .nil)) <;>
      · show prep.1.store.funcs[_]? = _
        rw [hfuncs]; rfl

end Silmaril.Proofs.Wasm.Examples.SatAccept

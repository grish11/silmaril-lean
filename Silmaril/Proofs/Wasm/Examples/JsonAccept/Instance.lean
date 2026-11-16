module

public import Silmaril.Wasm.Examples.JsonAccept.Thms
public import Silmaril.Wasm.Examples.JsonAccept.Instance.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Verify.FnSpec.Thms

/-!
# The JSON-subset acceptor, instantiated: proofs

The specification's allocation of `prog` (`prepare?` into the empty import store) is computed
by kernel evaluation (`decide +kernel`, `rfl`). It has no imports, no data segments and no start
function, and one function at address `0`, which is `accept`, with one memory at address `0`.
Every spec instance is therefore this one. A store reached by writing input bytes into the
memory still has `accept` at address `0`, so the verified `accept_returns_one_iff` applies to
every run of the embedding of `Silmaril.Wasm.Game.Accept.Export`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.JsonAccept Silmaril.Wasm.Game.Accept Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Numerics (Profile)

abbrev mt0 := specMT
abbrev prep := specPrep

set_option maxRecDepth 100000

theorem t_valid : (validate? prog).isSome = true := by decide +kernel
theorem t_prep : (prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0)).isSome = true := by decide +kernel
theorem t_start : prep.2 = none := by decide +kernel
theorem t_code : prep.1.code.isEmpty = true := by decide +kernel
theorem t_nf : prep.1.store.funcs.length = 1 := by decide +kernel
theorem t_fcode : prep.1.store.funcs.map FuncInst.code = [.wasm prog.funcs[0]] := rfl
theorem t_ty : prep.1.store.funcs.map (fun fi => FnType.ofDefType? fi.type) =
    [some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩] := by decide +kernel
theorem t_fmems : prep.1.store.funcs.map (fun fi => fi.module.mems) = [[0]] := by decide +kernel
theorem t_frame_mems : prep.1.frame.module.mems = [0] := by decide +kernel
theorem t_export : exportFunc? prep.1.frame.module "accept" = some 0 := by decide +kernel
theorem t_addrs : exportFuncAddrs prep.1.frame.module = [0] := by decide +kernel
theorem t_nmems : prep.1.store.mems.length = 1 := by decide +kernel

theorem validate_eq : validate? prog = some mt0 := by
  obtain ⟨mt, h⟩ := Option.isSome_iff_exists.1 t_valid
  simp [mt0, specMT, h]

theorem prepare_eq : prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0) = some prep := by
  obtain ⟨x, h⟩ := Option.isSome_iff_exists.1 t_prep
  simp [prep, specPrep, h]

/-- The function of the instance. -/
theorem exists_fi : ∃ fi : FuncInst Nat, prep.1.store.funcs = [fi] ∧
    fi.code = .wasm prog.funcs[0] ∧
    FnType.ofDefType? fi.type = some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩ ∧
    fi.module.mems = [0] := by
  obtain ⟨fi, h⟩ := List.length_eq_one_iff.1 t_nf
  have h1 := t_fcode; have h2 := t_ty; have h3 := t_fmems
  rw [h] at h1 h2 h3
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1 h2 h3
  exact ⟨fi, h, h1, h2, h3⟩

/-- **Every spec instance of `prog` is the computed one.** -/
theorem spec_instance_eq {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance prog mt I c₀) : mt = mt0 ∧ c₀ = prep.1 := by
  have hmt : mt = mt0 := Option.some.inj (hI.valid.symm.trans validate_eq)
  subst hmt
  obtain ⟨c, st, hp, hc0, -, -⟩ := hI.prepared
  have h := Option.some.inj (hp.symm.trans prepare_eq)
  have hc : c = prep.1 := congrArg Prod.fst h
  have hs : st = prep.2 := congrArg Prod.snd h
  refine ⟨rfl, ?_⟩
  rw [hc0, hc, hs, t_start]; rfl

/-- The bytes `[p, p + n)` as read by `accept` are the memory's. -/
theorem segment_eq {B : ByteArray} {p n : Nat} (h : p + n ≤ B.size) :
    memSegment B p n = some (segment B p n) := by
  simp only [memSegment, Execution.Memory.readBytes, h, ↓reduceIte, Option.map_some,
    Option.some.injEq]
  apply List.ext_getElem
  · simp [segment, bytesN]; omega
  · intro i h1 h2
    have hi : i < n := by simpa [segment, bytesN] using h2
    simp only [segment, bytesN, List.getElem_map, List.getElem_range, bd]
    rw [Silmaril.Wasm.Logic.Core.load_eq (by omega)]
    simp only [Option.getD_some, Silmaril.Wasm.Logic.Core.bytesAt,
      Silmaril.Wasm.Logic.Core.leNat]
    simp [ByteArray.data_extract, List.take_one, Array.getElem_toList]
    have hlt : p + i < B.data.size := by
      have : B.size = B.data.size := rfl
      omega
    rw [Array.getElem?_eq_getElem hlt]
    simp only [Option.elim_some, Nat.mod_eq_of_lt (B.data[p + i]).toNat_lt]
    exact (UInt8.ofNat_toNat).symm

theorem steps_from_prep {P : Profile} {host : HostSemantics Nat} {s₀ : Store Nat} {f₀ : Frame}
    (h : Steps P host prep.1 ⟨s₀, f₀, vals []⟩) : s₀ = prep.1.store := by
  have hc : prep.1 = ⟨prep.1.store, prep.1.frame, vals []⟩ := by
    have : prep.1.code = [] := List.isEmpty_iff.1 t_code
    cases hp : prep.1 with
    | mk st fr cd => rw [hp] at this; subst this; rfl
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, hs, -⟩
  · rw [hc] at he
    exact (congrArg Config.store he).symm.trans rfl |>.symm.symm ▸ by
      cases he; rfl
  · rw [hc] at hs
    exact absurd hs Silmaril.Wasm.Execution.Core.Step.not_vals

/-- **The embedded acceptor answers by the automaton**: any run of the embedding that answers
`r` has `r = 1` iff the input is an integer text. -/
theorem exportAnswered_iff {P : Profile} {Hosts : Set (HostSemantics Nat)} {r : BitVec 32}
    {w : List UInt8} (hw : w ∈ exportAnswered P Hosts prog "accept" r) :
    (r = 1 ↔ w ∈ intText) := by
  obtain ⟨mt, I, c₀, hI, host, -, s₀, f₀, hsteps, a, ma, mt', B₀, B, p, n, hexp, hm0, hs0, hseg,
    hov, hbeh⟩ := hw
  obtain ⟨-, rfl⟩ := spec_instance_eq hI
  have hs₀ := steps_from_prep hsteps
  subst hs₀
  rw [t_export] at hexp; cases hexp
  rw [t_frame_mems] at hm0; cases hm0
  have hb : p.toNat + n.toNat ≤ B.size := by
    unfold memSegment Execution.Memory.readBytes at hseg
    split_ifs at hseg with h
    · exact h
    · cases hseg
  rw [segment_eq hb] at hseg
  cases hseg
  obtain ⟨fi, hfuncs, hcode, hty, hmems⟩ := exists_fi
  have hfi : (prep.1.store.setMem 0 ⟨mt', B⟩).funcs[0]? = some fi := by
    show prep.1.store.funcs[0]? = some fi
    rw [hfuncs]; rfl
  have hmem : MemAt (prep.1.store.setMem 0 ⟨mt', B⟩) fi.module 0 mt' B :=
    ⟨by rw [hmems]; rfl, by rw [Silmaril.Wasm.Verify.getElem?_mems_setMem_self, hs0]; rfl⟩
  have he := FnType.expand_of_ofDefType? hty
  rcases hbeh with ⟨⟨s', f', code⟩, res, hs, hcode', hr⟩ | ⟨h, -⟩
  · cases res with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hr
      subst hr
      simp only [Result.toAdmin] at hcode'
      subst hcode'
      have := accept_returns_one_iff hfi hcode he (by simp [Ty.length, Ty.ofList])
        (by simp [Ty.length, Ty.ofList]) hmem hb hov hs
      rw [← this]
      constructor
      · rintro rfl; rfl
      · intro h
        simp only [Val.i32, List.cons.injEq, Val.num.injEq, and_true] at h
        cases h; rfl
    | trap => cases hr
    | throw _ => cases hr
  · cases h

abbrev inst := specInst

theorem t_imports : mt0.imports = [] := by decide +kernel

/-- **`prog` has a spec instance** (so the embedding is not vacuous). -/
theorem isSpecInstance : IsSpecInstance prog mt0 inst prep.1 where
  valid := validate_eq
  funcImports := by rw [t_imports]; simp
  importTypes := by rw [t_imports]; exact .nil
  prepared := ⟨prep.1, prep.2, prepare_eq, by rw [t_start]; rfl, rfl, t_addrs⟩
  exportTypes := by
    obtain ⟨fi, hfuncs, -, hty, -⟩ := exists_fi
    exact .cons ⟨fi, by show prep.1.store.funcs[0]? = _; rw [hfuncs]; rfl, hty⟩ .nil

end Silmaril.Proofs.Wasm.Examples.JsonAccept

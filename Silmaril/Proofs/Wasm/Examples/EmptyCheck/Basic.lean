module

public import Silmaril.Wasm.Examples.EmptyCheck.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Examples.Wat.Thms

/-!
# The empty checker as a core Wasm module: proofs

* `spec_vc`: `check` meets `spec` (`wasm_vc`); `check_returns`: every returning run of
  `$invoke` on in-bounds arguments returns `0`, store unchanged.
* `check_total`: total correctness of the loop-free body (`wpc_sound_total`), hence
  `check_exists`: some run returns `0`.
* The specification's allocation of `prog` is computed by kernel evaluation, as for
  `Silmaril.Wasm.Examples.JsonAccept`: every spec instance is that one (`spec_instance_eq`),
  and it exists (`isSpecInstance`).
* `exportAnswered_zero`: a run of the embedding only ever answers `0`;
  `exportAnswered_of_run`: every input shorter than `2 ^ 32` has a run answering `0`.

New proofs, following `Silmaril.Proofs.Wasm.Examples.JsonAccept`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.EmptyCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Verify
open Silmaril.Wasm.Logic.Words Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Game
open Silmaril.Wasm.Game.Accept Silmaril.Wasm.Examples.EmptyCheck
open Silmaril.Wasm.Numerics (Profile)

/-! ## The function -/

theorem spec_vc : spec.vc prog.funcs[0] := by
  wasm_vc [spec, prog]

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}
  {p n : BitVec 32}

theorem check_returns (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    s' = s ∧ res = [.i32 0] := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) spec_vc hc he
    (fun _ => by simp [spec, FnSpec.mem, hps]) (by simpa [spec, FnSpec.mem] using hrs) (p, n)
  obtain ⟨res', hres, hpost⟩ := FSpecValid.invoke_vals hv ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ hs
  cases hres
  obtain ⟨hs', hr⟩ := hpost ma mt B hmem
  exact ⟨hs'.trans (setMem_eq_self hmem.2), hr⟩

set_option linter.unusedSimpArgs false in
theorem check_total {fi : FuncInst Nat} {a : Nat} (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (x : BitVec 32 × BitVec 32) : TFSpecAt P host a (spec.fspec fi a x) := by
  obtain ⟨p, n⟩ := x
  refine TFSpecAt.of_body (fun s args h => h.1) hcode he
    (fun s args h => by rw [h.2.1]; simp [spec, FnSpec.mem, hps]) ?_
  rintro s args ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ f vs₀
  refine Silmaril.Wasm.Logic.VC.wpc_sound_total (fun _ _ _ _ => True) 0 prog.funcs[0].body
    (by decide +kernel) _ s _ [] ?_
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    wat_vc_simp, prog]
  refine bodyPostT_normal (by simpa using hrs.symm) ⟨_, rfl, ?_⟩
  rintro ma' mt' B' ⟨h1, h2⟩
  obtain ⟨hm0, hm⟩ := hmem
  rw [hm0] at h1; cases h1
  rw [hm] at h2; cases h2
  exact ⟨(setMem_eq_self hm).symm, rfl⟩

theorem TSafe.exists_exit {Q : Silmaril.Wasm.Logic.Core.Post Nat} {c : Config Nat}
    (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hex _ ih =>
    obtain ⟨c₁, h₁⟩ := hex
    obtain ⟨c', hs, rest⟩ := ih c₁ h₁
    exact ⟨c', .head h₁ hs, rest⟩

theorem check_exists (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s, f', vals [.i32 0]⟩ := by
  have ht := check_total (P := P) (host := host) (a := a) hcode he hps hrs (p, n)
  have hsafe : TSafe P host (callPost {} [] ((spec.fspec fi a (p, n)).post s [.i32 p, .i32 n]))
      (invoke s a [.i32 p, .i32 n]) :=
    ht s [.i32 p, .i32 n] ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ {} []
      (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial
  obtain ⟨⟨s', f', code⟩, hs, o, hex, hq⟩ := TSafe.exists_exit hsafe
  obtain ⟨-, hq⟩ := hq
  rcases hq with ⟨res, rfl, res', hres, hpost⟩ | ⟨rfl, res', hres, -⟩ | ⟨x, rfl, res', hres, -⟩
  · cases hres
    obtain ⟨hs', hr⟩ := hpost ma mt B hmem
    simp only [List.nil_append] at hex
    simp only at hex hs'
    subst hex
    rw [hs'.trans (setMem_eq_self hmem.2), hr] at hs
    exact ⟨f', hs⟩
  · cases hres
  · cases hres

/-! ## The instance -/

abbrev mt0 := specMT
abbrev prep := specPrep
abbrev inst := specInst

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
theorem t_export : exportFunc? prep.1.frame.module "check" = some 0 := by decide +kernel
theorem t_addrs : exportFuncAddrs prep.1.frame.module = [0] := by decide +kernel
theorem t_nmems : prep.1.store.mems.length = 1 := by decide +kernel
theorem t_imports : mt0.imports = [] := by decide +kernel

theorem validate_eq : validate? prog = some mt0 := by
  obtain ⟨mt, h⟩ := Option.isSome_iff_exists.1 t_valid
  simp [mt0, specMT, h]

theorem prepare_eq : prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0) = some prep := by
  obtain ⟨x, h⟩ := Option.isSome_iff_exists.1 t_prep
  simp [prep, specPrep, h]

theorem exists_fi : ∃ fi : FuncInst Nat, prep.1.store.funcs = [fi] ∧
    fi.code = .wasm prog.funcs[0] ∧
    FnType.ofDefType? fi.type = some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩ ∧
    fi.module.mems = [0] := by
  obtain ⟨fi, h⟩ := List.length_eq_one_iff.1 t_nf
  have h1 := t_fcode; have h2 := t_ty; have h3 := t_fmems
  rw [h] at h1 h2 h3
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1 h2 h3
  exact ⟨fi, h, h1, h2, h3⟩

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

theorem isSpecInstance : IsSpecInstance prog mt0 inst prep.1 where
  valid := validate_eq
  funcImports := by rw [t_imports]; simp
  importTypes := by rw [t_imports]; exact .nil
  prepared := ⟨prep.1, prep.2, prepare_eq, by rw [t_start]; rfl, rfl, t_addrs⟩
  exportTypes := by
    obtain ⟨fi, hfuncs, -, hty, -⟩ := exists_fi
    exact .cons ⟨fi, by show prep.1.store.funcs[0]? = _; rw [hfuncs]; rfl, hty⟩ .nil

theorem prep_eq : prep.1 = ⟨prep.1.store, prep.1.frame, vals []⟩ := by
  have : prep.1.code = [] := List.isEmpty_iff.1 t_code
  cases hp : prep.1 with
  | mk st fr cd => rw [hp] at this; subst this; rfl

theorem steps_from_prep {s₀ : Store Nat} {f₀ : Frame}
    (h : Steps P host prep.1 ⟨s₀, f₀, vals []⟩) : s₀ = prep.1.store := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, hs, -⟩
  · rw [prep_eq] at he
    cases he; rfl
  · rw [prep_eq] at hs
    exact absurd hs Silmaril.Wasm.Execution.Core.Step.not_vals

/-! ## The embedding -/

/-- **A run of the embedding only ever answers `0`.** -/
theorem exportAnswered_zero {Hosts : Set (HostSemantics Nat)} {r : BitVec 32} {w : List UInt8}
    (hw : w ∈ exportAnswered P Hosts prog "check" r) : r = 0 := by
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
  obtain ⟨fi, hfuncs, hcode, hty, hmems⟩ := exists_fi
  have hfi : (prep.1.store.setMem 0 ⟨mt', B⟩).funcs[0]? = some fi := by
    show prep.1.store.funcs[0]? = some fi
    rw [hfuncs]; rfl
  have hmem : MemAt (prep.1.store.setMem 0 ⟨mt', B⟩) fi.module 0 mt' B :=
    ⟨by rw [hmems]; rfl, by rw [getElem?_mems_setMem_self, hs0]; rfl⟩
  have he := FnType.expand_of_ofDefType? hty
  rcases hbeh with ⟨⟨s', f', code⟩, res, hs, hcode', hr⟩ | ⟨h, -⟩
  · cases res with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hr
      subst hr
      simp only [Result.toAdmin] at hcode'
      subst hcode'
      have := (check_returns hfi hcode he (by simp [Ty.length, Ty.ofList])
        (by simp [Ty.length, Ty.ofList]) hmem hb hov hs).2
      simp only [Val.i32, List.cons.injEq, Val.num.injEq, and_true] at this
      cases this; rfl
    | trap => cases hr
    | throw _ => cases hr
  · cases h

theorem memSegment_length {B : ByteArray} {p n : Nat} {w : List UInt8}
    (h : memSegment B p n = some w) : w.length = n := by
  unfold memSegment at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Array.length_toList]
  exact Execution.Memory.readBytes_size B b p n hb

theorem memSegment_ofList (w : List UInt8) :
    memSegment ⟨w.toArray⟩ 0 w.length = some w := by
  simp [memSegment, Execution.Memory.readBytes, ByteArray.size, ByteArray.data_extract]

theorem exportAnswered_length {Hosts : Set (HostSemantics Nat)} {r : BitVec 32}
    {w : List UInt8} (hw : w ∈ exportAnswered P Hosts prog "check" r) : w.length < 2 ^ 32 := by
  obtain ⟨mt, I, c₀, hI, host, hhost, s₀, f₀, hsteps, a, ma, mt', B₀, B, p, n, hexp, hm0, hs0,
    hseg, hov, hbeh⟩ := hw
  rw [memSegment_length hseg]; exact n.isLt

/-- **Every admitted input gets an answer, `0`.** -/
theorem exportAnswered_of_run {Hosts : Set (HostSemantics Nat)} (hh : host ∈ Hosts)
    {w : List UInt8} (hw : w.length < 2 ^ 32) : w ∈ exportAnswered P Hosts prog "check" 0 := by
  have h0 : 0 < prep.1.store.mems.length := by rw [t_nmems]; decide
  obtain ⟨mi₀, hmi⟩ : ∃ mi₀, prep.1.store.mems[0]? = some mi₀ :=
    ⟨_, List.getElem?_eq_getElem h0⟩
  obtain ⟨fi, hfuncs, hcode, hty, hmems⟩ := exists_fi
  set B : ByteArray := ⟨w.toArray⟩
  set n : BitVec 32 := BitVec.ofNat 32 w.length
  have hn : n.toNat = w.length := by
    simp only [n, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hw
  have hBs : B.size = w.length := by simp [B, ByteArray.size]
  have hseg : memSegment B (0 : BitVec 32).toNat n.toNat = some w := by
    rw [hn]; exact memSegment_ofList w
  have hfi : (prep.1.store.setMem 0 ⟨mi₀.type, B⟩).funcs[0]? = some fi := by
    show prep.1.store.funcs[0]? = some fi
    rw [hfuncs]; rfl
  have hmem : MemAt (prep.1.store.setMem 0 ⟨mi₀.type, B⟩) fi.module 0 mi₀.type B :=
    ⟨by rw [hmems]; rfl, by rw [getElem?_mems_setMem_self, hmi]; rfl⟩
  have hb : (0 : BitVec 32).toNat + n.toNat ≤ B.size := by rw [hn, hBs]; simp
  have hov : (0 : BitVec 32).toNat + n.toNat < 2 ^ 32 := by rw [hn]; simpa using hw
  obtain ⟨f', hs⟩ := check_exists (P := P) (host := host) hfi hcode
    (FnType.expand_of_ofDefType? hty) (by simp [Validation.Ty.length, Validation.Ty.ofList])
    (by simp [Validation.Ty.length, Validation.Ty.ofList]) hmem hb hov
  refine ⟨mt0, inst, prep.1, isSpecInstance, host, hh, prep.1.store, prep.1.frame,
    by rw [← prep_eq], 0, 0, mi₀.type, mi₀.bytes, B, 0, n, t_export, by rw [t_frame_mems]; rfl,
    by rw [hmi], hseg, hov, ?_⟩
  exact .inl ⟨_, .values _, hs, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Examples.EmptyCheck

module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Root
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Exports
public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Thms
public import Silmaril.Wasm.Component.DecoderBridge.ParamName.Thms
public import Silmaril.Wasm.Component.DecoderBridge.InstExport.Thms
public import Silmaril.Wasm.Component.InstTests.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# The named IR reading: the theorems (proofs)

* `parseComponentN_ok`, `parseComponentN_of_ok`: the named IR reading succeeds exactly when the
  IR reading does, with the same component;
* `named_of_decode`: the named IR signature is the named reference reading (`lowerSig_of_toRef`
  through the common AST, `decoders_factor`);
* `erase_of_decode`: on `InFrag` it erases to the IR's imports and exports (`refReadN_of_refRead`
  and `relW_of_decode`);
* `rootChecked_of_named`: on `InFrag`, the named imports `hostIN` give `RootChecked`
  (`rootChecked_of_refReadN`);
* `startAdequacyNamed_of_checked`, `startAdequacyNamed_of_multiImpFrag`: the start goal on the
  named IR from the corrected start goal, and on `MultiImpFrag`;
* `parseN_paramName`, `parseN_starts`, `parseN_instExport` (`kernel_rfl`): the named readings of
  the test binaries;
* `inFrag_noInstExport`, `exportNames_of_decode`: the restriction on exported instances.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Proofs.Wasm.Component.DecoderBridge (decoders_factor)
open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

theorem parseComponentN_eq {b : ByteArray} {n : NComp} (h : parseComponentN b = .ok n) :
    ∃ a, Binary.parse b = .ok a ∧ lower a = .ok n.comp ∧ n.sig = Lower.lowerSig a := by
  unfold parseComponentN lowerN at h
  cases hp : Binary.parse b with
  | error e => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | ok a =>
    simp only [hp, bind, Except.bind, pure, Except.pure] at h
    cases hl : lower a with
    | error e => simp [hl] at h
    | ok c =>
      simp only [hl, Except.ok.injEq] at h
      subst h
      exact ⟨a, rfl, hl, rfl⟩

theorem parseComponentN_ok {b : ByteArray} {n : NComp} (h : parseComponentN b = .ok n) :
    parseComponent b = .ok n.comp := by
  obtain ⟨a, hp, hl, -⟩ := parseComponentN_eq h
  simp [parseComponent, hp, hl, bind, Except.bind, pure, Except.pure]

theorem parseComponentN_of_ok {b : ByteArray} {c : Comp CoreMod} (h : parseComponent b = .ok c) :
    ∃ n, parseComponentN b = .ok n ∧ n.comp = c := by
  unfold parseComponent at h
  cases hp : Binary.parse b with
  | error e => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | ok a =>
    simp only [hp, bind, Except.bind, pure, Except.pure] at h
    refine ⟨⟨c, Lower.lowerSig a⟩, ?_, rfl⟩
    simp [parseComponentN, lowerN, hp, h, bind, Except.bind, pure, Except.pure]

theorem toRef_of_parseN {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) :
    ∃ a, toRef a = .ok r ∧ lower a = .ok n.comp ∧ n.sig = Lower.lowerSig a := by
  obtain ⟨a, hp, hl, hs⟩ := parseComponentN_eq hc
  unfold decodeRef at hr
  rw [hp] at hr
  exact ⟨a, hr, hl, hs⟩

theorem named_of_decode {b : ByteArray} {n : NComp} {r : RefComponent} {N : RN}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hN : refReadN r = some N) :
    n.imports = N.imports ∧ n.exports = N.exports := by
  obtain ⟨a, ht, -, hs⟩ := toRef_of_parseN hc hr
  have h := lowerSig_of_toRef ht hN
  rw [← hs] at h
  exact ⟨by simp [NComp.imports, h], by simp [NComp.exports, h]⟩

theorem refReadN_of_inFrag {r : RefComponent} (h : InFrag r) : ∃ N, refReadN r = some N := by
  unfold InFrag inFrag at h
  cases hR : refRead r with
  | none => simp [hR] at h
  | some R =>
    obtain ⟨N, hN, -⟩ := refReadN_of_refRead hR
    exact ⟨N, hN⟩

theorem erase_of_decode {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    NIface.erase n.imports = n.comp.imports ∧
      n.exports.map (fun p => (p.1, p.2.erase)) = n.comp.exports.map fun e => (e.name, e.ty) := by
  obtain ⟨R, hR, hi, he, -⟩ := Silmaril.Proofs.Wasm.Component.DecoderBridge.relW_of_decode
    (parseComponentN_ok hc) hr hf
  obtain ⟨N, hN, hnr⟩ := refReadN_of_refRead hR
  obtain ⟨h1, h2⟩ := named_of_decode hc hr hN
  rw [h1, h2, hi, he]
  exact ⟨hnr.imports, hnr.exports⟩

theorem rootChecked_of_named {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r)
    (hi : n.imports = hostIN) : RootChecked r := by
  obtain ⟨N, hN⟩ := refReadN_of_inFrag hf
  exact rootChecked_of_refReadN hN ((named_of_decode hc hr hN).1 ▸ hi)

theorem hostI_of_named {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r)
    (hi : n.imports = hostIN) : n.comp.imports = hostI := by
  rw [← (erase_of_decode hc hr hf).1, hi]
  rfl

theorem startAdequacyNamed_of_checked (h : Task.startAdequacyChecked) : Task.startAdequacyNamed :=
  fun b n r t nm ws hc hr hv hf hi hex hu hp =>
    h b n.comp r t nm ws (parseComponentN_ok hc) hr hv hf (rootChecked_of_named hc hr hf hi)
      (hostI_of_named hc hr hf hi) hex hu hp

theorem startAdequacyNamed_of_multiImpFrag (b : ByteArray) (n : NComp) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (nm : String)
    (ws : List Silmaril.Wasm.Component.Val)
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r)
    (hv : ∃ ct, Valid Features.p2 r ct) (hf : InFrag r) (hm : MultiImpFrag r)
    (hi : n.imports = hostIN) (hex : (n.comp.exports.map (·.name)).head? = some nm)
    (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hp : instPlay (F := sigU) t .ready ++
      [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
        n.comp.denI (Binary.coreModSemI (profile neverFail))) :
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(nm, [])] :=
  startAdequacyChecked_of_multiImpFrag b n.comp r t nm ws (parseComponentN_ok hc) hr hv hf
    (rootChecked_of_named hc hr hf hi) hm (hostI_of_named hc hr hf hi) hex hu hp

/-! ## The test binaries -/

/-- The named signature of `paramname.wasm`. -/
def sigY : NSig := ⟨[("f", ⟨[("y", .u32)], []⟩)], [("get", ⟨[], [.u32]⟩)]⟩

/-- The named signature of `starts.wasm`. -/
def sigX : NSig := ⟨hostIN, [("get", ⟨[], [.u32]⟩)]⟩

/-- The named signature of `instexport.wasm`. -/
def sigI : NSig := ⟨hostIN, [("i#get", ⟨[], [.u32]⟩)]⟩

theorem parseN_paramName : parseComponentN paramNameBytes = .ok ⟨startsComp, sigY⟩ := by
  kernel_rfl

theorem parseN_starts : parseComponentN startsBytes = .ok ⟨startsComp, sigX⟩ := by
  kernel_rfl

theorem parseN_instExport : parseComponentN instExportBytes = .ok ⟨instExportComp, sigI⟩ := by
  kernel_rfl

/-! ## Exported instances -/

theorem inFrag_noInstExport {r : RefComponent} (h : InFrag r) : NoInstExport r := by
  unfold InFrag inFrag at h
  cases hR : refRead r with
  | none => simp [hR] at h
  | some R =>
    unfold refRead at hR
    unfold NoInstExport noInstExport
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨R1, R2, hs⟩ := Silmaril.Proofs.Wasm.Component.DecoderBridge.foldlM_each hR d hd
    split
    · simp [refStep] at hs
    · rfl

theorem exportNames_of_decode {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hn : NoInstExport r) :
    n.exports.map (·.1) = refFuncExportNames r := by
  obtain ⟨a, ht, -, hs⟩ := toRef_of_parseN hc hr
  simp only [NComp.exports, hs]
  exact exportNames_of_toRef ht hn

theorem exportNames_ir_of_inFrag {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    n.comp.exports.map (·.name) = refFuncExportNames r := by
  have h1 := congrArg (List.map Prod.fst) (erase_of_decode hc hr hf).2
  simp only [List.map_map] at h1
  rw [← exportNames_of_decode hc hr (inFrag_noInstExport hf)]
  exact h1.symm

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Named

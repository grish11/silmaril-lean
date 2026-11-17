module

public import Silmaril.Wasm.Cfg.SessionCheck.Defs
public import Silmaril.Wasm.Cfg.Session.Thms
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Interp.ExampleX.Thms
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# Checking the CFG session's domain (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.SessionCheck

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Component Silmaril.Wasm.Cfg.Session Silmaril.Wasm.Cfg.SessionCheck

/-! ## Components: congruence on the core instances they use -/

section Comp

variable {M : Type} [CoreModule M] {p : M → Prop} {C C' : DCoreSem M}

mutual
/-- **Denotations depend only on the core instances used**: core semantics agreeing on every
core instance of the component give the same divergence-observing denotation. -/
theorem denUD_congrIn (h : ∀ m, p m → C.sem m = C'.sem m) :
    ∀ c : Comp M, CompIn p c → c.denUD C = c.denUD C'
  | .mk I ns xs, hc => by
    simp only [Comp.denUD]
    rw [nodes_congrIn h ns I.length _ hc]

theorem nodes_congrIn (h : ∀ m, p m → C.sem m = C'.sem m) :
    ∀ (ns : List (Node M)) (e : Nat) {X : Games.Sig.{0}} (D : Games.DStrategy X sigU),
      NodesIn p ns → denNodesD C e ns D = denNodesD C' e ns D
  | [], _, _, _, _ => by simp only [denNodesD]
  | n :: ns, e, _, D, hns => by
    simp only [denNodesD]
    rw [node_congrIn h n e hns.1]
    exact nodes_congrIn h ns _ _ hns.2

theorem node_congrIn (h : ∀ m, p m → C.sem m = C'.sem m) :
    ∀ (n : Node M) (e : Nat), NodeIn p n → n.denD C e = n.denD C' e
  | .core m args, e, hm => by
    simp only [Node.denD, dcoreNode, h m hm]
  | .inst c args, e, hc => by
    simp only [Node.denD]
    rw [denUD_congrIn h c hc]
end

end Comp

/-! ## The executable check of the domain -/

theorem storeChkE_of_B {H : Type} {ext : ExtArity H} {F : List (FuncInst H)}
    (hb : ExampleX.storeChkEB ext F = true) : StoreChkE ext F := by
  intro a fi fn ps rs hfi hcode hty
  have h : ExampleX.funcChkEB ext F fi = true :=
    List.all_eq_true.mp hb fi (List.mem_of_getElem? hfi)
  simpa only [ExampleX.funcChkEB, hcode, hty] using h

theorem wasmFuncsT_of_B {s : Store Nat} (hb : wasmFuncsB s.funcs = true) : WasmFuncsT s := by
  intro a fi hfi
  have h := List.all_eq_true.mp hb fi (List.mem_of_getElem? hfi)
  cases hc : fi.code with
  | wasm fn =>
    rw [hc] at h
    obtain ⟨⟨ps, rs⟩, hty⟩ := Option.isSome_iff_exists.mp h
    exact ⟨fn, ps, rs, rfl, hty⟩
  | host hh => rw [hc] at h; cases h

theorem export_type_of_B {I : ScalarInstance} (hb : exportsB I = true) (j : Fin I.exports.length) :
    ∃ fi : FuncInst Nat, I.store.funcs[I.addr j]? = some fi ∧
      Validation.Expand fi.type (I.exports.get j).toComp := by
  simp only [exportsB, Bool.and_eq_true] at hb
  have h := List.all_eq_true.mp hb.2 j (List.mem_finRange j)
  cases hf : I.store.funcs[I.addr j]? with
  | none => rw [hf] at h; cases h
  | some fi =>
    rw [hf] at h
    exact ⟨fi, rfl, Validation.Expand.iff.2 (of_decide_eq_true h)⟩

theorem addrs_length_of_B {I : ScalarInstance} (hb : exportsB I = true) :
    I.addrs.length = I.exports.length := by
  simp only [exportsB, Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.1

/-- **The executable check gives the CFG session's domain**: for a validated module without
imports, instantiated into the empty store with no start function, a scalar instance at that store
passing `hfCheck` is in the domain. -/
theorem hfOk_of_check {I : ScalarInstance} {mod : Module} {mt : Validation.CModuleType}
    {c : Config Nat} (hv : Validation.validate? mod = some mt) (himp : mt.imports = [])
    (hp : prepare? evalConst? ({} : Store Nat) mod [] = some (c, none))
    (hs : I.store = c.store) (hb : hfCheck I = true) : HFOk I I.store := by
  simp only [hfCheck, Bool.and_eq_true, List.isEmpty_iff] at hb
  obtain ⟨⟨⟨hnil, hchk⟩, hwasm⟩, hexp⟩ := hb
  have hvalid : ∃ xtE xtI, Validation.ModuleOk mod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Nat)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hv, by rw [himp]; exact .nil⟩
  have hinst := (prepare?_sound (P := SingleThreaded.profile fun _ _ _ _ => false)
    (host := SingleThreaded.divHost) evalConst?_evalSound hp hvalid).2
  have hcfg : ConfigOk c [] := Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty hinst
  have hsok : StoreOk I.store := by rw [hs]; exact SingleThreaded.ConfigOk.storeOk hcfg
  have hW := wasmFuncsT_of_B hwasm
  refine ⟨hnil, ⟨hsok, addrs_length_of_B hexp, export_type_of_B hexp, ?_⟩, hW,
    storeChkE_of_B hchk⟩
  intro a fi h hfi hc
  obtain ⟨fn, -, -, hcode, -⟩ := hW a fi hfi
  rw [hcode] at hc; cases hc

end Silmaril.Wasm.Cfg.Proofs.SessionCheck

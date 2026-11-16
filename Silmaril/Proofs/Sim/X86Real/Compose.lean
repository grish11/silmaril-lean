module

public import Silmaril.Proofs.Sim.X86Real.Core
public import Silmaril.Proofs.Sim.X86Real.AccessG
public import Silmaril.Proofs.Sim.X86Real.AccessM

/-!
# Composition: accessor contracts + shared core ⇒ methods, for each representation

* `core_of_accessors`: for **any** representation `ρ` with `Rep.Laws`, an instance of `simG`'s
  code (`CodeOK`) whose five accessors meet their contracts runs `$alu` and `i_alu_rr` per their
  contracts (64-bit add/sub/cmp; total correctness). The core is verified once (`Core.lean`).
* `accessorsG`, **`iAluRR_G`**: for representation G the accessor contracts are proved
  (`AccessG.lean`), so `i_alu_rr` of the instantiated `simG` meets `iAluRRSpec (repG mi)` with no
  assumption beyond the instance facts.
A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Number of parameters / results of the covered functions. -/
def nPar : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 1 | 6 => 1 | 9 => 1 | 10 => 5 | 11 => 2
  | 12 => 3 | 17 => 4 | 42 => 4 | _ => 0

/-- Number of results. -/
def nRes : Nat → Nat
  | 0 => 1 | 2 => 1 | 5 => 1 | 6 => 1 | 9 => 1 | 11 => 1 | 17 => 1 | _ => 0

/-- The instance runs the defined functions of `m` (code, module instance, function types). -/
structure CodeOK (m : Module) (I : Inst H) : Prop where
  code : ∀ k ∈ coreKs, (I.fi k).code = .wasm (fn m k)
  mod : ∀ k ∈ coreKs, (I.fi k).module = I.mi
  ty : ∀ k ∈ coreKs, ∃ ps rs, Silmaril.Wasm.Validation.Expand (I.fi k).type (.func ps rs) ∧
    ps.length = nPar k ∧ rs.length = nRes k

/-- **The shared core, once for every representation**: accessor contracts ⇒ `$alu`,
`i_alu_rr`. -/
theorem core_of_accessors {ρ : Rep H} (hL : ρ.Laws) {I : Inst H} (hinj : I.Inj)
    {m : Module} (hc : CodeOK m I) (hm : ∀ k ∈ [5, 6, 9, 10, 11, 12, 17, 42], fn m k = fn simG k)
    (hacc : ∀ k ∈ [0, 1, 2, 3, 4], TFSpecAt P host (I.A k) (entry ρ I k).2) :
    TFSpecAt P host (I.A 17) (aluSpec ρ I) ∧ TFSpecAt P host (I.A 42) (iAluRRSpec ρ I) := by
  have T : ∀ k, k ∈ coreKs → ∃ ps rs, Silmaril.Wasm.Validation.Expand (I.fi k).type (.func ps rs) ∧
      ps.length = nPar k ∧ rs.length = nRes k := hc.ty
  have C : ∀ k, k ∈ [5, 6, 9, 10, 11, 12, 17, 42] → (I.fi k).code = .wasm (fn simG k) :=
    fun k hk => by rw [← hm k hk]; exact hc.code k (by simp at hk; simp [coreKs]; omega)
  have h5 : TFSpecAt P host (I.A 5) (maskSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 5 (by decide); mask_total (C 5 (by decide)) e p r
  have h6 : TFSpecAt P host (I.A 6) (sbitSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 6 (by decide); sbit_total (C 6 (by decide)) e p r
  have h9 : TFSpecAt P host (I.A 9) (paritySpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 9 (by decide); parity_total (C 9 (by decide)) e p r
  have Γ1 : (specsOf ρ I ks1).TValid P host := tvalid1 hacc h5 h6 h9
  have h10 : TFSpecAt P host (I.A 10) (fresSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 10 (by decide)
    fres_total hL Γ1 hinj (C 10 (by decide)) (hc.mod 10 (by decide)) e p r
  have h11 : TFSpecAt P host (I.A 11) (rdSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 11 (by decide)
    rd_total Γ1 hinj (C 11 (by decide)) (hc.mod 11 (by decide)) e p r
  have h12 : TFSpecAt P host (I.A 12) (wrSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 12 (by decide)
    wr_total hL Γ1 hinj (C 12 (by decide)) (hc.mod 12 (by decide)) e p r
  have Γ2 : (specsOf ρ I ks2).TValid P host := specsOf_tvalid ks2_sub (by
    simp only [ks2, List.forall_mem_cons]
    exact ⟨hacc 0 (by decide), hacc 1 (by decide), hacc 2 (by decide), hacc 3 (by decide),
      hacc 4 (by decide), h5, h6, h9, h10, h11, h12, fun _ h => absurd h List.not_mem_nil⟩)
  have h17 : TFSpecAt P host (I.A 17) (aluSpec ρ I) :=
    let ⟨_, _, e, p, r⟩ := T 17 (by decide)
    alu_total Γ2 hinj (C 17 (by decide)) (hc.mod 17 (by decide)) e p r
  have Γ3 : (specsOf ρ I ks3).TValid P host := specsOf_tvalid ks3_sub (by
    simp only [ks3, List.forall_mem_cons]
    exact ⟨hacc 0 (by decide), hacc 1 (by decide), hacc 2 (by decide), hacc 3 (by decide),
      hacc 4 (by decide), h5, h6, h9, h10, h11, h12, h17, fun _ h => absurd h List.not_mem_nil⟩)
  obtain ⟨_, _, e42, p42, r42⟩ : ∃ ps rs, Silmaril.Wasm.Validation.Expand (I.fi 42).type (.func ps rs) ∧
      ps.length = nPar 42 ∧ rs.length = nRes 42 := T 42 (by decide)
  exact ⟨h17, iAluRR_total hL Γ3 hinj (C 42 (by decide)) (hc.mod 42 (by decide)) e42 p42 r42⟩

/-- **The five G accessors of the instantiated `simG` meet their contracts.** -/
theorem accessorsG {I : Inst H} (hc : CodeOK simG I) :
    ∀ k ∈ [0, 1, 2, 3, 4], TFSpecAt P host (I.A k) (entry (repG I.mi) I k).2 := by
  intro k hk
  have T : ∀ k, k ∈ coreKs → ∃ ps rs, Silmaril.Wasm.Validation.Expand (I.fi k).type (.func ps rs) ∧
      ps.length = nPar k ∧ rs.length = nRes k := hc.ty
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, e, p, r⟩ := T 0 (by decide)
    exact rgetG_total (hc.code 0 (by decide)) (hc.mod 0 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 1 (by decide)
    exact rsetG_total (hc.code 1 (by decide)) (hc.mod 1 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 2 (by decide)
    exact fgetG_total (hc.code 2 (by decide)) (hc.mod 2 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 3 (by decide)
    exact fsetG_total (hc.code 3 (by decide)) (hc.mod 3 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 4 (by decide)
    exact fset6G_total (hc.code 4 (by decide)) (hc.mod 4 (by decide)) e p r

/-- **`i_alu_rr` of the instantiated `simG` (representation G)**: 64-bit add/sub/cmp, total
correctness, no assumption beyond the instance facts. -/
theorem iAluRR_G {I : Inst H} (hinj : I.Inj) (hc : CodeOK simG I) :
    TFSpecAt P host (I.A 42) (iAluRRSpec (repG I.mi) I) :=
  (core_of_accessors (repG_laws I.mi) hinj hc (fun _ _ => rfl) (accessorsG hc)).2

/-- The core functions of `simM` are those of `simG` (same quoted text, checked by `rfl`). -/
theorem fn_simM_core : ∀ k ∈ [5, 6, 9, 10, 11, 12, 17, 42], fn simM k = fn simG k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **`i_alu_rr` of the instantiated `simM` (representation M)**, given M's accessor contracts. -/
theorem iAluRR_M_of {I : Inst H} (hinj : I.Inj) (hc : CodeOK simM I) (hL : (repM I.mi : Rep H).Laws)
    (hacc : ∀ k ∈ [0, 1, 2, 3, 4], TFSpecAt P host (I.A k) (entry (repM I.mi) I k).2) :
    TFSpecAt P host (I.A 42) (iAluRRSpec (repM I.mi) I) :=
  (core_of_accessors hL hinj hc fn_simM_core hacc).2

/-- The same as a partial-correctness `FSpecValid` (the form of `Ctx.Valid`). -/
theorem iAluRR_G_valid {I : Inst H} (hinj : I.Inj) (hc : CodeOK simG I) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host (I.A 42) (iAluRRSpec (repG I.mi) I) :=
  (iAluRR_G hinj hc).valid


/-- **The five M accessors of the instantiated `simM` meet their contracts.** -/
theorem accessorsM {I : Inst H} (hc : CodeOK simM I) :
    ∀ k ∈ [0, 1, 2, 3, 4], TFSpecAt P host (I.A k) (entry (repM I.mi) I k).2 := by
  intro k hk
  have T : ∀ k, k ∈ coreKs → ∃ ps rs, Silmaril.Wasm.Validation.Expand (I.fi k).type (.func ps rs) ∧
      ps.length = nPar k ∧ rs.length = nRes k := hc.ty
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, e, p, r⟩ := T 0 (by decide)
    exact rgetM_total (hc.code 0 (by decide)) (hc.mod 0 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 1 (by decide)
    exact rsetM_total (hc.code 1 (by decide)) (hc.mod 1 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 2 (by decide)
    exact fgetM_total (hc.code 2 (by decide)) (hc.mod 2 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 3 (by decide)
    exact fsetM_total (hc.code 3 (by decide)) (hc.mod 3 (by decide)) e p r
  · obtain ⟨_, _, e, p, r⟩ := T 4 (by decide)
    exact fset6M_total (hc.code 4 (by decide)) (hc.mod 4 (by decide)) e p r

/-- **`i_alu_rr` of the instantiated `simM` (representation M)**: unconditional given the
instance facts. -/
theorem iAluRR_M {I : Inst H} (hinj : I.Inj) (hc : CodeOK simM I) :
    TFSpecAt P host (I.A 42) (iAluRRSpec (repM I.mi) I) :=
  iAluRR_M_of hinj hc (repM_laws I.mi) (accessorsM hc)

/-- **G ≡ M for `i_alu_rr`**: an instance of `simG` and an instance of `simM` both run
`i_alu_rr` (64-bit add/sub/cmp) with the same effect on their read-backs — `iAluRRSpec` is one
function of the read-back, instantiated with `repG` resp. `repM`. -/
theorem iAluRR_GM {IG IM : Inst H} (hG : IG.Inj) (cG : CodeOK simG IG) (hM : IM.Inj)
    (cM : CodeOK simM IM) :
    TFSpecAt P host (IG.A 42) (iAluRRSpec (repG IG.mi) IG) ∧
      TFSpecAt P host (IM.A 42) (iAluRRSpec (repM IM.mi) IM) :=
  ⟨iAluRR_G hG cG, iAluRR_M hM cM⟩

end Silmaril.Sim.X86Real

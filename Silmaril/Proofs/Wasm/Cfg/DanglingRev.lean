module

public import Silmaril.Wasm.Cfg.DanglingExn.Thms
public import Silmaril.Wasm.Cfg.CfgInst.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms

@[expose] public section

/-!
# The reverse inclusion for dangling host exceptions: the legal part (proofs)

`cfgInstTripleU I` (the CFG instance triple at the unrestricted universal host) contains the
legal CFG instance triple `cfgInstTripleL I`: `instHostL I` answers are `instHostU I` answers
(`coreHostRel_L_le_U`), and the open restriction and the view are monotone. With `instTripleL_agree`
the legal Core triple is contained in `cfgInstTripleU` on the domain; with the forward inclusion
`cfgInstTripleU_sub` this sandwiches `cfgInstTripleU` between the legal and the full instance
triple. Without imports the two ends coincide.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingRev

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Abstract (coreHostRel)
open Silmaril.Wasm.Abstract.NodeBridge (viewTriple)
open Silmaril.Wasm.Abstract.InstSession (instTripleS)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {I : ScalarInstance}

theorem coreHostRel_L_le_U : ∀ m o, coreHostRel (instHostL I) m o → coreHostRel (instHostU I) m o
  | _, .answer _, ⟨h₁, h₂, _⟩ => ⟨h₁, h₂, fun _ _ _ => trivial⟩
  | _, .diverge, ⟨h₁, h₂, _⟩ => ⟨h₁, h₂, fun _ _ _ => trivial⟩

/-- **The legal CFG instance triple is contained in the unrestricted one**, componentwise, at
every store and question. -/
theorem cfgInstTripleL_sub_U (s : Store Nat) (a : I.F.Op) :
    (cfgInstTripleL I).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (cfgInstTripleL I).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (cfgInstTripleL I).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, ⟨hy, hc⟩, hF, hv⟩
    exact ⟨y, ⟨hy, fun c hc' => coreHostRel_L_le_U _ _ (hc c hc')⟩, hF, hv⟩
  · rintro x ⟨y, ⟨hy, hc⟩, hF, hv⟩
    exact ⟨y, ⟨hy, fun c hc' => coreHostRel_L_le_U _ _ (hc c hc')⟩, hF, hv⟩
  · rintro ω ⟨ω', hω, hv⟩
    exact ⟨ω', hostObsInf_mono coreHostRel_L_le_U hω, hv⟩

variable {o : GrowOracle}

/-- **The legal instance triple is contained in the unrestricted CFG instance triple**, on the
domain, at a deterministic profile. -/
theorem instTripleL_sub_cfgInstTripleU {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    (instTripleL I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleL I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleL I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a := by
  obtain ⟨h₁, h₂, h₃⟩ := instTripleL_agree (o := o) hd a
  obtain ⟨k₁, k₂, k₃⟩ := cfgInstTripleL_sub_U (I := I) s a
  exact ⟨h₁ ▸ k₁, h₂ ▸ k₂, h₃ ▸ k₃⟩

/-- **Without imports, the unrestricted CFG instance triple is the instance triple**, on the
domain, at a deterministic profile. -/
theorem instTripleS_agree_cfgInstTripleU_of_nil (h : I.imports = []) {s : Store Nat}
    (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a := by
  have hL := instTripleL_eq_of_nil h (profile o)
  obtain ⟨b₁, b₂, b₃⟩ := instTripleL_sub_cfgInstTripleU (o := o) hd a
  obtain ⟨f₁, f₂, f₃⟩ := cfgInstTripleU_sub (P := profile o) hd a
  rw [hL] at b₁ b₂ b₃
  exact ⟨Set.Subset.antisymm b₁ f₁, Set.Subset.antisymm b₂ f₂, Set.Subset.antisymm b₃ f₃⟩

end Silmaril.Wasm.Cfg.Proofs.DanglingRev

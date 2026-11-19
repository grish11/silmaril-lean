module

public import Silmaril.Wasm.Cfg.DanglingExn.Thms
public import Silmaril.Wasm.Cfg.CfgInst.Thms
import Silmaril.Proofs.Wasm.Cfg.DanglingRev

@[expose] public section

/-!
# The reverse inclusion for dangling host exceptions: what is proved (theorems)

`DanglingExn.cfgInstTripleU_sub` (native/CFG ⊆ Core) is the forward inclusion at the
unrestricted universal host `instHostU I`, on `CfgInst.InstDom I s`, every profile. The reverse
inclusion (`instTripleS I P ⊆ cfgInstTripleU I`) is proved here **only on the legal part**:

* `cfgInstTripleL_sub_U`: the legal CFG instance triple is contained in the unrestricted one
  (every store and question; `instHostL I` answers are `instHostU I` answers);
* `instTripleL_sub_cfgInstTripleU`: on `InstDom I s`, at a deterministic profile `profile o`,
  every finished behaviour, pending call and productive stream of the **legal** instance triple
  `instTripleL I` (Core witnesses whose host throws name exceptions of the call store) is one of
  `cfgInstTripleU I`. So, per question and componentwise,
  `instTripleL I (profile o) ⊆ cfgInstTripleU I ⊆ instTripleS I (profile o)`;
* `instTripleS_agree_cfgInstTripleU_of_nil`: without imports the ends coincide, and
  `cfgInstTripleU I` **is** the instance triple (`AgreeAt`, every observation) on `InstDom`.

The reverse inclusion for Core behaviours with a dangling host throw (outside `instTripleL`)
is `DanglingBack.instTripleS_sub_cfgInstTripleU`, on well-formed stores in the checker's
instruction profile; with #988 it gives the per-question equality
`DanglingBack.instTripleS_agree_cfgInstTripleU`.
-/

namespace Silmaril.Wasm.Cfg.DanglingRev

open Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Abstract.InstSession (instTripleS)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {I : ScalarInstance} {o : GrowOracle}

/-- **The legal CFG instance triple is contained in the unrestricted one.** -/
theorem cfgInstTripleL_sub_U (s : Store Nat) (a : I.F.Op) :
    (cfgInstTripleL I).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (cfgInstTripleL I).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (cfgInstTripleL I).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a :=
  Proofs.DanglingRev.cfgInstTripleL_sub_U s a

/-- **The legal instance triple is contained in the unrestricted CFG instance triple**, on the
domain, at a deterministic profile. -/
theorem instTripleL_sub_cfgInstTripleU {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    (instTripleL I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleL I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleL I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a :=
  Proofs.DanglingRev.instTripleL_sub_cfgInstTripleU hd a

/-- **Without imports, the unrestricted CFG instance triple is the instance triple**, on the
domain, at a deterministic profile. -/
theorem instTripleS_agree_cfgInstTripleU_of_nil (h : I.imports = []) {s : Store Nat}
    (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a :=
  Proofs.DanglingRev.instTripleS_agree_cfgInstTripleU_of_nil h hd a

end Silmaril.Wasm.Cfg.DanglingRev

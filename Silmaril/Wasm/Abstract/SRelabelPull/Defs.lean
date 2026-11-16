module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Games.AnsPull.Defs

/-!
# The session relabelling as a generic pull

`srelabel : Move E (ifaceSig ts) → Move E (ssig ts)` keeps import moves and export questions and
sends the answer `v` to `f` to `sAns f v`. Since `ssig ts = ⟨(ifaceSig ts).Op, fun _ => Res ts ⊕
PUnit⟩`, it is the generic upper answer relabelling `ansMove sAns`
(`Silmaril.Games.AnsMap`, `srelabel_eq_ansMove`). Hence it is compatible with the legality automata
through `posAns` (`pullData_srelabel`, from `pullData_ansMove`), and the generic pull
`DStrategy.pull srelabel posAns pullData_srelabel` (`Silmaril.Games.DPull`) is defined.

This header imports only `InstSession.Defs` and `AnsPull.Defs`, so `InstSessionD.Defs` can import
it to define `spullD` as that generic pull. `Silmaril.Wasm.Abstract.SRelabelPull.Thms` shows the
current `spull` and `spullD` are the generic pulls (`spull_eq_pull`, `spullD_eq_pull`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games
open Silmaril.Wasm.Game Silmaril.Wasm.Component.Reference

variable {E : Sig.{0}} {ts : List FnType}

/-- **`srelabel` is the generic upper answer relabelling** along `sAns`. -/
theorem srelabel_eq_ansMove :
    (srelabel : Move E (ifaceSig ts) → Move E (ssig ts)) =
      ansMove (B' := fun _ => Res ts ⊕ PUnit.{1}) sAns := by
  funext o; rcases o with e | (q | ⟨q, v⟩) <;> rfl

/-- **`srelabel` is compatible with the legality automata**, through `posAns`. -/
theorem pullData_srelabel :
    PullData (srelabel : Move E (ifaceSig ts) → Move E (ssig ts)) posAns := by
  rw [srelabel_eq_ansMove]; exact pullData_ansMove _

end Silmaril.Wasm.Abstract.InstSession

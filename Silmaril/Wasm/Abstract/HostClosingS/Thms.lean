module

public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Close

/-!
# Session closing: theorems

The session closure `wasmEvFunXPS` keeps the store of every trap, and erasing those stores
(`StratSession.eraseEnd`, `.ret (.inr ()) s ↦ .trap`) gives exactly the canonical closure
`wasmEvFunXP`, with the same logs:

* `wasmEvFunXPS_erase_le`: a session behaviour erases to a canonical one. A trap answer of the
  session relation is, in the canonical relation, a cut call (an answer of more values than the
  callee's result arity, then a trap), and the callee's store-keeping trap, which resolves the trap
  answer by `Shape.Subst.int`, erases to a trap resolving the cut call by `Shape.Subst.intTrap`.
* `le_wasmEvFunXPS_erase`: a canonical behaviour is an erased session one. A call resolved by
  `Shape.Subst.intTrap` (a cut call, or an ordinary one) is reached, and answering it by the
  callee's trap ends the session run; a cut call is never resolved by a return
  (`wasmEvFunXP_ret_len`).
* `wasmEvFunXPS_erase`: the equality of the two; `eraseTrap_wasmEvFunXPS`: the same through
  `StratSession.eraseTrap`, whatever the pending calls and productive streams.
* `wasmEvFunXPS_ne_trap`, `wasmEvFunXPS_noPlainTrap`: the session closure has no plain trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Games.Abstract.StratSession (eraseEnd eraseTrap NoPlainTrap)

variable {H : Type}

/-- **A session behaviour erases to a canonical behaviour**, with the same log. -/
theorem wasmEvFunXPS_erase_le {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : y ∈ wasmEvFunXPS s p) : (y.1, eraseEnd y.2) ∈ wasmEvFunXP s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_erase hy

/-- **A canonical behaviour is an erased session behaviour**, with the same log. -/
theorem le_wasmEvFunXPS_erase {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : y ∈ wasmEvFunXP s p) :
    ∃ y' ∈ wasmEvFunXPS s p, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2 :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_lift hy

/-- **Erasing the stores of traps projects the session closure onto the canonical closure.** -/
theorem wasmEvFunXPS_erase (s : Store H) (p : Nat × List Val) :
    (fun x => (x.1, eraseEnd x.2)) '' wasmEvFunXPS s p = wasmEvFunXP s p := by
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact wasmEvFunXPS_erase_le hy'
  · intro hy
    obtain ⟨y', hy', h1, h2⟩ := le_wasmEvFunXPS_erase hy
    exact ⟨y', hy', Prod.ext h1 h2⟩

/-- The projection as `StratSession.eraseTrap`, for any pending calls and productive streams. -/
theorem eraseTrap_wasmEvFunXPS
    (P : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val))
    (I : Silmaril.Games.Abstract.PInf (wasmHostSig H) (Store H) (Nat × List Val)) :
    (eraseTrap (wasmEvFunXPS, P, I)).1 = wasmEvFunXP :=
  funext fun s => funext fun p => wasmEvFunXPS_erase s p

/-- **The session closure has no plain trap**: every trap keeps its store. -/
theorem wasmEvFunXPS_ne_trap {s : Store H} {p : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} : (cs, .trap) ∉ wasmEvFunXPS s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_ne_trap

theorem wasmEvFunXPS_noPlainTrap
    (P : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val))
    (I : Silmaril.Games.Abstract.PInf (wasmHostSig H) (Store H) (Nat × List Val)) :
    NoPlainTrap (wasmEvFunXPS, P, I) :=
  fun _ _ _ => wasmEvFunXPS_ne_trap

end Silmaril.Wasm.Abstract

module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Pend
public import Silmaril.Wasm.Abstract.OpenStrat.Defs

/-!
# The session triple projects onto the open canonical triple (proofs)

`wasmEvFunDXP` is `Shape.closeDLog`: the closure, and behaviours ending in `div`
(`closeDLog_nondiv`). So erasing trap stores sends `wasmEvFunDXPS` (the session closure and the
same divergent behaviours) onto `wasmEvFunDXP` (`erase_wasmEvFunDXPS`); the pending calls agree
(`pendS_toH`, `pend_toS`) and the productive streams are shared, so `StratSession.eraseTrap`
sends `sessionTripleXP` to `openTripleXP` (`eraseTrap_sessionTripleXP`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingS

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Games.Abstract.StratSession (eraseEnd eraseTrap NoPlainTrap)

section Generic

universe u

variable {sh : Silmaril.Games.Abstract.Shape.{u}} {m : sh.OpenMod}
  {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop} {f : sh.F} {s : sh.S} {a : sh.A f}
  {y : CallBeh sh.E sh.S (sh.B f)}

/-- A behaviour of `closeDLog` that does not diverge is a behaviour of the closure. -/
theorem closeDLog_nondiv (h : y ∈ Shape.closeDLog m LDL f s a) (hy : y.2 ≠ .div) :
    y ∈ Shape.close m f s a := by
  rcases h with (h | ⟨hd, -⟩) | ⟨hd, -⟩
  · exact h
  · exact absurd hd hy
  · exact absurd hd hy

theorem close_sub_closeDLog (h : y ∈ Shape.close m f s a) : y ∈ Shape.closeDLog m LDL f s a :=
  .inl (.inl h)

end Generic

variable {H : Type}

/-- **Erasing trap stores sends `wasmEvFunDXPS` onto `wasmEvFunDXP`.** -/
theorem erase_wasmEvFunDXPS (s : Store H) (p : Nat × List Val) :
    (fun x => (x.1, eraseEnd x.2)) '' wasmEvFunDXPS s p = wasmEvFunDXP s p := by
  ext y
  constructor
  · rintro ⟨⟨c, e⟩, hy' | ⟨hd, hm⟩, rfl⟩
    · exact close_sub_closeDLog (close_erase hy')
    · obtain rfl : e = .div := hd
      exact hm
  · intro hy
    by_cases hd : y.2 = .div
    · obtain ⟨c, e⟩ := y
      obtain rfl : e = .div := hd
      exact ⟨(c, .div), .inr ⟨rfl, hy⟩, rfl⟩
    · obtain ⟨y', hy', h1, h2⟩ := close_lift (closeDLog_nondiv hy hd)
      exact ⟨y', .inl hy', Prod.ext h1 h2⟩

/-- **The session triple erases to the open canonical triple.** -/
theorem eraseTrap_sessionTripleXP : eraseTrap (sessionTripleXP (H := H)) = openTripleXP := by
  have hp : wasmEvPendXPS (H := H) = wasmEvPendXP :=
    funext fun _ => funext fun _ => Set.ext fun _ => ⟨pendS_toH, pend_toS⟩
  have hf : (fun s a => (fun x => (x.1, eraseEnd x.2)) '' wasmEvFunDXPS (H := H) s a) =
      wasmEvFunDXP := funext fun s => funext fun p => erase_wasmEvFunDXPS s p
  simp only [eraseTrap, sessionTripleXP, openTripleXP, hf, hp]

/-- **The session triple has no plain trap.** -/
theorem sessionTripleXP_noPlainTrap : NoPlainTrap (sessionTripleXP (H := H)) := by
  rintro s p c (h | ⟨hd, -⟩)
  · exact close_ne_trap h
  · cases hd

end Silmaril.Proofs.Wasm.Abstract.HostClosingS

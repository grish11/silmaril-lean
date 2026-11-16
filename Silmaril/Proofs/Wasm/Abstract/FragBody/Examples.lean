module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Basic

/-!
# The fragment denotation: examples

`spinFunc` (`loop br 0 end`) denotes silent divergence, computed from the
Elgot iteration of its loop, and hence has no fragment run. `exampleSum`
(a counting loop) denotes its run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA Silmaril.Elgot.ITree

variable {E : Sig.{0}} {S : Type 1}

theorem loopG_spin : loopG (E := E) (S := S) none [.br 0 []] = fun p => pure (.inr p) := by
  funext p
  have hs : Seq p.1.down none [.br 0 []] (.brk 0 p.1.down none) :=
    .abrupt (.br .nil) trivial
  refine (loopG_of (v := .ok (.inr ⟨p.1.down⟩, p.2)) ?_).trans rfl
  rw [run_bind_ok (seq_den (E := E) hs p.2)]
  rfl

theorem run_spinFunc (s : S) : run' (denFunc spinFunc ⟨[]⟩ : M E S _) s = diverge := by
  simp only [denFunc, spinFunc, List.map_nil, ↓reduceIte]
  apply run_bind_diverge
  simp only [denSeq]
  apply run_bind_diverge
  have h : run' (den (.loop none [.br 0 []]) (spinFunc.initLocals []) : M E S OutE) s =
      (Silmaril.Elgot.iter (loopG (E := E) none [.br 0 []]) (⟨spinFunc.initLocals []⟩, s) :
        Tree (SigEv E) _) := by
    simp only [den]; exact run_iter _ _ _
  refine h.trans ?_
  rw [loopG_spin]
  exact iterate_forever _

theorem spinFunc_no_run (o : FOut) : ¬ spinFunc.Run [] o := by
  have h := run_spinFunc (E := Silmaril.Games.Sig.empty) (S := PUnit.{2}) ⟨⟩
  exact (denFunc_exact (E := Silmaril.Games.Sig.empty) (S := PUnit.{2}) spinFunc [] ⟨⟩).2.1 h o

end Silmaril.Proofs.Wasm.Abstract.FragBody

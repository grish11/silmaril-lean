module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Coalescing.Defs
public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section
namespace Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang.Coalescing

open Silmaril.Machine.Region.X86.SqliteStrLength
  (Register Operation ReturnSlot DataReady model entryStore)
open Silmaril.Machine.Region.X86.SqliteStrLength.Clang
open Silmaril.X86
open Silmaril.SSA.LambdaRTL

theorem firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry)
    (actual : FnContract.FirstReturn Open.isa entry final) :
    ∃ terminal preRet,
      preRet.core.rip = entry.core.rip + offset terminal ∧ Open.step preRet = some final ∧
      (obs <$> graph.run (model entry.memory) (entryStore entry)) = some (terminal, final.core.read .rax) ∧
      (obs <$> coalesced.toRegion.evalRTL (model entry.memory) (entryStore entry)) =
        some (coalesceReturns terminal, final.core.read .rax) ∧ final.memory = entry.memory := by
  obtain ⟨_, terminal, _, preRet, _, _, _, _, _, _, retPC, retStep, original, frame⟩ :=
    bridge_of_firstReturn loaded saved ready actual
  refine ⟨terminal, preRet, retPC, retStep, original, ?_, frame⟩
  rw [← CFG.run_eq_toRegion, coalesced, CFG.run_relabel_of_check _ _ _ _ (by decide), Functor.map_map]
  have mapped := congrArg (Option.map (fun out => (coalesceReturns out.1, out.2))) original
  change Option.map (fun out => (coalesceReturns out.1, out.2))
    (Option.map obs (graph.run (model entry.memory) (entryStore entry))) = _ at mapped
  rw [Option.map_map] at mapped
  exact mapped

end Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang.Coalescing

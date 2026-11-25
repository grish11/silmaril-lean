module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Coalescing.Defs
public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.Proofs.Machine.Region.X86.SqliteStrLength.Clang.Coalescing

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength.Clang

open Silmaril.X86
open Silmaril.SSA.LambdaRTL

theorem coalesceReturns_check : graph.relabelLookupCheck coalesceReturns = true := by decide

/-- The observation view aliases a live arm label and fails the syntax check. -/
theorem exitView_rejected : graph.relabelLookupCheck exitView = false := by decide

/-- The coalescing maps the outward label and preserves the payload and complete store. -/
theorem coalesced_run {M : Type → Type} {α : Type} [Monad M] [LawfulMonad M]
    (m : Model Operation M α) (store : Register → α) :
    coalesced.run m store = (fun out => (coalesceReturns out.1, out.2)) <$> graph.run m store :=
  CFG.run_relabel_of_check m coalesceReturns graph store coalesceReturns_check

private theorem view_coalesced (label : Label) : exitView (coalesceReturns label) = exitView label := by
  cases label <;> rfl

/-- With the shared exit view, the normalized Clang region and the GCC region agree
on exit, payload and complete store, including failure of the modeled read. -/
theorem coalesced_viewed_region (entry : MState) :
    (fun out => (exitView out.1, out.2)) <$> coalesced.toRegion.evalRTL (model entry.memory) (entryStore entry) =
      SqliteStrLength.graph.toRegion.evalRTL (model entry.memory) (entryStore entry) := by
  rw [← CFG.run_eq_toRegion, ← CFG.run_eq_toRegion, coalesced_run, Functor.map_map]
  simpa only [Function.comp_def, view_coalesced] using viewed_run entry

/-- A machine first return has the same payload in the original CFG and normalized
region. The original CFG label still identifies the actual machine RET. -/
theorem coalesced_firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry)
    (actual : FnContract.FirstReturn Open.isa entry final) :
    ∃ terminal preRet,
      preRet.core.rip = entry.core.rip + offset terminal ∧ Open.step preRet = some final ∧
      (obs <$> graph.run (model entry.memory) (entryStore entry)) = some (terminal, final.core.read .rax) ∧
      (obs <$> coalesced.toRegion.evalRTL (model entry.memory) (entryStore entry)) =
        some (coalesceReturns terminal, final.core.read .rax) ∧ final.memory = entry.memory :=
  Proofs.Machine.Region.X86.SqliteStrLength.Clang.Coalescing.firstReturn loaded saved ready actual

end Silmaril.Machine.Region.X86.SqliteStrLength.Clang

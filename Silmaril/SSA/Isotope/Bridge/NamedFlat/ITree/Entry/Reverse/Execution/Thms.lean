module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Execution.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL (CFG obs)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic (Transfer stepSSA)
open Silmaril.Elgot (iter)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)

/-- Reading the live-outs at the actual exit equals projecting the final
store of the emitted mutable program. -/
theorem observeAttached_eq (M : Model (κ := κ) Events P.Instr) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr)
    (record : Ty.denote Atoms (Region.packedInputType I.context.toList)) :
    observeAttached M I fields source record = LiveOut.observe M I fields source record := by
  simp only [observeAttached, withLiveOut, LiveOut.observe, LiveOut.observeRaw, CFG.Cyclic.LiveOut.run_project,
    ← bind_pure_comp, bind_assoc, pure_bind]

/-- Packet closure lifts the one-step carried-store isolation to the entire
cyclic continuation. The lexical table can use any base environment. -/
theorem Lowered.resumeAttached_eq {I : Interface κ V K} {fields : K → List (V × Ty κ)}
    {blocks : Nat} {code : FiniteCFG P.Instr blocks I.exits.length I.slots}
    (a : Lowered I fields code) (M : Model (κ := κ) Events P.Instr)
    (pending : Transfer V K (Value (Sigma Atoms))) (base : V → Value (Sigma Atoms)) :
    let table := (withLiveOut fields a.source).blocks
    obs <$> iter (CFG.Cyclic.step (treeModel M.raw) table) pending =
      iter (stepSSA (treeModel M.raw) table base) (obs pending) :=
  CFG.Cyclic.iter_obs_of_step_encoding (treeModel M.raw) _ obs _
    (CFG.Cyclic.RoundTrip.step_packetClosed_obs (treeModel M.raw) _ a.closed base) pending

section Numbered

open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open NamedFlat.Entry.Reverse.Straight (encode_captures)

variable {n blocks : Nat} {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)} {code : FiniteCFG P.Instr blocks exits.length n}

local notation "Input" => Ty.denote Atoms (Region.packedInputType context.toList)

omit [DecidableEq V] in
/-- Resume the actual versioned dispatcher at the same label and packet.
The saved fields come from the supplied record when the carried store
agrees on the selected slots. The assertion is local to this transfer and
the Elgot step equation covers every later edge, including backedges. -/
theorem Lowered.resumeSaved_eq (a : Lowered (numberedInterface context exits external) fields code)
    (M : Model (κ := κ) Events P.Instr) (slots : List (Fin n)) (record : Input)
    (pending : Transfer Register K (Value (Sigma Atoms)))
    (route : Versioning.destinations (withLiveOut fields a.source) pending.1 =
      some (slots.map fun i => (⟨i.val⟩ : Register)))
    (agrees : ∀ i ∈ slots, pending.2.2 ⟨i.val⟩ = inputEnv context record i.val) :
    let attached := withLiveOut fields a.source
    let model := treeModel M.raw
    let input := store (fun i : Fin n => ((⟨i.val⟩ : Register), 0)) context record
    let packet := .pair pending.2.1
      (slots.foldr (fun i tail => .pair (inputEnv context record i.val) tail) .unit)
    obs <$> iter (CFG.Cyclic.step model attached.blocks) pending =
      iter (stepSSA model (Versioning.compile attached).blocks input) (pending.1, packet) := by
  dsimp only
  rw [← encode_captures a M slots record pending route agrees]
  exact CFG.Cyclic.iter_obs_of_step_encoding (treeModel M.raw) _ _ _
    (Versioning.step_commutes (treeModel M.raw) ⟨fun _ _ => rfl⟩ _ _) pending

end Numbered

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

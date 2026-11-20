module

public import Silmaril.Wasm.Game.HandleAccept.Families.Matrix
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Game.HandleAccept.Families Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted
  Silmaril.Wasm.Game.HandleAccept.MemSound.Tab Silmaril.Wasm.Game.HandleAccept.Memory

private theorem hinted_decode (call : Callout) :
    ((hintedTab.lookup ("sexp", "hinted")).bind (AtomDec.decode · call)) = Callout.hinted call := by
  rw [hintedTab_hinted]
  unfold segs2 Callout.hinted
  generalize call.args = operands
  split <;> split <;> simp_all [Option.map_bind, Option.map_map, Function.comp_def]
  rename_i hintPtr hintLen octetsPtr octetsLen notShape
  exact (notShape hintPtr hintLen octetsPtr octetsLen rfl rfl rfl rfl).elim

private theorem hinted_write (call : Callout) (reply : HostReply) :
    tabWrite hintedTab {} call reply = hintedWrite {} call reply := by
  by_cases isHinted : call.imp = ("sexp", "hinted")
  · have lookup : hintedTab.lookup ("sexp", "hinted") = some (.seg2 hintedD2) := rfl
    have decoded : (AtomDec.seg2 hintedD2).decode call = Callout.hinted call := by
      simpa only [lookup, Option.bind_some] using hinted_decode call
    simp [tabWrite, hintedWrite, isHinted, lookup, decoded]
  · by_cases isBlob : call.imp = ("sexp", "blob")
    · simp [tabWrite, hintedWrite, isBlob, hintedTab, AtomDec.decode, hintedDec]
      cases replyI32 reply <;> cases call.bytes32 <;> rfl
    · have hintCheck : (call.imp == ("sexp", "hinted")) = false := beq_eq_false_iff_ne.mpr isHinted
      have blobCheck : (call.imp == ("sexp", "blob")) = false := beq_eq_false_iff_ne.mpr isBlob
      simp [tabWrite, hintedWrite, isHinted, isBlob, hintedTab, List.lookup, hintCheck, blobCheck]

theorem hinted_roles : tabRoles hintedTab {} = hintedRoles {} := by
  have answer : tabWrite hintedTab {} = hintedWrite {} := funext fun call => funext (hinted_write call)
  unfold tabRoles hintedRoles
  rw [answer]
  rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Families

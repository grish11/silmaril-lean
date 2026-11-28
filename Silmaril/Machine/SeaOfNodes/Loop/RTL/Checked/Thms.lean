module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Correctness

/-! # Exact admission and finite-return correspondence -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp entry model word)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin step)
open Silmaril.SSA.RVSDG (Wires)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow ValueSort)
open Silmaril.SSA.SeaOfNodes.Loop (Graph)

theorem schedule_eq {args : List PortTy} (body : Dataflow WordOp args [] headerSigs)
    (p : Profile) (update : Wires args [] [.value word, .value word])
    (guard : Wires args [[.value word], [.value word]] [.value word, .value word])
    (decoded : decodeSchedule body = some p)
    (addresses : scheduleAddresses body = scheduleAddresses (schedule p update guard)) :
    body = schedule p update guard :=
  Proofs.schedule_eq body p update guard decoded addresses

theorem decode_schedule {args : List PortTy} (p : Profile)
    (update : Wires args [] [.value word, .value word])
    (guard : Wires args [[.value word], [.value word]] [.value word, .value word]) :
    decodeSchedule (schedule p update guard) = some p :=
  Proofs.decode_schedule p update guard

theorem graph_eq_of_provenance {inputs carried : List (ValueSort Unit)}
    {g h : Graph WordOp inputs carried [] headerSigs word}
    (header : g.header = h.header) (agree : provenance g = provenance h) : g = h :=
  Proofs.graph_eq_of_provenance header agree

theorem recognize_eq_some_iff (g : WordLoop) (p : Profile) :
    recognize g = some p ↔ g = p.graph :=
  Proofs.recognize_eq_some_iff g p

/-- A successful lowering witnesses the profile with exactly the input graph. -/
theorem lower_eq_some_iff (g : WordLoop) (target : Prog Reg) :
    lower g = some target ↔ ∃ p : Profile, g = p.graph ∧ target = p.lower := by
  simp only [lower, Option.map_eq_some_iff, recognize_eq_some_iff]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

theorem lower_wellFormed {g : WordLoop} {target : Prog Reg} (ok : lower g = some target) :
    target.WellFormed := by
  obtain ⟨p, _, rfl⟩ := (lower_eq_some_iff g target).mp ok
  simpa [Prog.WellFormed, Profile.lower] using p.lower_wellFormed

/-- Every finite machine return from a checked graph and every finite native
return agree on the word and the whole memory observation. -/
theorem lower_returns_iff {g : WordLoop} {target : Prog Reg} (ok : lower g = some target)
    (seed delta : Word) (initial final : Memory) (returned : List Word) :
    target.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, g.Returns model (entry seed delta) value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨p, rfl, rfl⟩ := (lower_eq_some_iff g target).mp ok
  exact p.lower_returns_iff seed delta initial final returned

/-- Exact machine steps expose the source backedge count for a checked graph. -/
theorem lower_stepsN_iff {g : WordLoop} {target : Prog Reg} (ok : lower g = some target)
    (seed delta : Word) (initial final : Memory) (returned : List Word) (n : Nat) :
    (∃ start finish, target.start 0 [seed, delta] initial = some start ∧
      StepsNWithin target [] (4 * n + 5) start finish ∧ step target finish = .returned returned final) ↔
    ∃ value : Word, g.ReturnsAfter model (entry seed delta) n
      (g.initial model (entry seed delta)) value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨p, rfl, rfl⟩ := (lower_eq_some_iff g target).mp ok
  exact p.lower_stepsN_iff seed delta initial final returned n

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked

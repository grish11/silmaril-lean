module

public import Silmaril.Project.CompilesTo.Explorer.Defs
public import Silmaril.Compiler.Explorer.Thms

/-!
# C functions as compilation problems: proofs

* `mapping_starts`: the function's mapping starts at the System V entry (point `0` is the entry
  with offset `0`, and the model reads `rip` from the open state).
* `refines_dwarf`: at every statement point, the correspondence relation implies the DWARF
  relation: the verified Core library's invariant (`StateMem.Inv`, inside `ObjectsAgree`) binds
  each object's symbol to its allocation and puts its definition in the Core slot, and
  `ObjectsAgree` puts the same definition in the DWARF frame slot.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.CompilesTo.Explorer

open Silmaril.Compiler.Explorer
open Silmaril.Project.CompilesTo
open Silmaril.Cerberus.Core.Dynamics

theorem mapping_starts (F : FnData) (I : Model) (k0 : List Frame)
    (hrip : ∀ m, (I.core m).rip = m.core.rip)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩) : (F.mapping I k0).Starts := by
  intro x0 s he
  have he' := he
  obtain ⟨-, args, hm, hc⟩ := he
  obtain ⟨-, env, hctl, -⟩ := hc
  refine ⟨⟨_, hp0, env, hctl⟩, ⟨_, hp0, ?_⟩, ⟨_, hp0, he'⟩⟩
  rw [hrip, hm.rip]
  simp

theorem refines_dwarf (F : FnData) (I : Model) (k0 : List Frame) :
    (F.mapping I k0).RefinesComorphism dwarf F.scope (fun _ => True) := by
  intro k _ x0 s x hr o ho
  obtain ⟨p, hp, hh⟩ := hr
  obtain ⟨p', hp', c, objs, hkind, hmem, hdef⟩ := ho
  rw [hp] at hp'
  cases hp'
  simp only [FnData.Holds, hkind] at hh
  obtain ⟨-, E, env, env₀, J, hctl, -, -, -, hagree⟩ := hh
  obtain ⟨ls, ds, hinv, -, -, hobjs⟩ := hagree
  obtain ⟨hdefined, hslot⟩ := hobjs o hmem
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hdefined hdef)
  obtain ⟨-, l, hl, hkey, hcore⟩ := hinv.defs _ d hd
  refine ⟨d.val 0, ⟨E, env, hctl, l.id, l.addr, ?_, hcore⟩, hslot d hd⟩
  exact hinv.env l hl o.sym hkey.symm

end Silmaril.Proofs.Project.CompilesTo.Explorer

end

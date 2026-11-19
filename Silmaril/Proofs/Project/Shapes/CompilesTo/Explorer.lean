module

public import Silmaril.Project.Shapes.CompilesTo.Explorer.Defs
public import Silmaril.Compiler.Explorer.Det.Thms
public import Silmaril.Proofs.Project.Shapes.CompilesTo

/-!
# C functions as compilation problems: proofs

* `mapping_starts`: the function's mapping starts at the System V entry (point `0` is the entry
  with offset `0`, and the model reads `rip` from the open state).
* `refines_dwarf`: at every point, the correspondence relation implies the relation the location
  semi-comorphism generates: the verified Core library's invariant (`StateMem.Inv`, inside
  `ObjectsAgree`) binds each object's symbol to its allocation and puts its definition in the
  Core slot, and `ObjectsAgree` puts the same definition in the frame slot.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer

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
    (F.mapping I k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) := by
  rintro k _ s ⟨x0, x⟩ hr o ho
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

open Silmaril.X86.SystemV.CApi (Arguments)

theorem compilation_inhabited (F : FnData) (I : Model) (haddr : F.addr < 2 ^ 64)
    (hen : Silmaril.Project.Shapes.SysV.Enterable I F.placement F.sig F.frame)
    (hint : ∀ k ∈ F.sig.arguments, k = .int32) (hlen : F.params.length = F.sig.arguments.length)
    (hsix : F.sig.arguments.length ≤ 6) (hnd : (F.params.map (·.1.key)).Nodup)
    (a : Arguments F.sig.arguments) (hsafe : (F.source []).Safe (F.cfn.canonicalEntry a)) :
    (F.compilation I []).toProblem.Inhabited := by
  obtain ⟨m, -, habi, hce⟩ := hen a
  exact ⟨F.cfn.canonicalEntry a, (m, m),
    ⟨rfl, rfl, a, Silmaril.Proofs.Project.Shapes.CompilesTo.machineEntry_of_callEntry haddr habi hce,
      Silmaril.Proofs.Project.Shapes.CompilesTo.canonicalEntry_entry F.cfn hint hlen hsix hnd a⟩,
    hsafe⟩

end Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer

end

module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Basic
public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Check

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: the image of typed code under the
denotation (`DenMor`) is closed under the operations on bodies the syntax is sent to.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall

variable {H : Type} {Γ : Ctx H}

theorem idP_mem (I : Iface) : (idP : PHom H Cfg ResP) ∈ DenMor Γ I (some I.h) :=
  ⟨[], rfl, denL_nil.symm⟩

theorem seqP_mem {I : Iface} {k : Nat} {o : Option Nat} {g₁ g₂ : PHom H Cfg ResP}
    (h₁ : g₁ ∈ DenMor Γ I (some k)) (h₂ : g₂ ∈ DenMor Γ ⟨I.env, k⟩ o) :
    seqP g₁ g₂ ∈ DenMor Γ I o := by
  obtain ⟨es₁, m₁, rfl⟩ := h₁
  obtain ⟨es₂, m₂, rfl⟩ := h₂
  exact ⟨es₁ ++ es₂, mor_comp m₁ m₂, (denL_append es₁ es₂).symm⟩

theorem seqP_stop_mem {I : Iface} {g₁ : PHom H Cfg ResP} (h₁ : g₁ ∈ DenMor Γ I none)
    (es₂ : List BExpr) : seqP g₁ (denL es₂) ∈ DenMor Γ I none := by
  obtain ⟨es₁, m₁, rfl⟩ := h₁
  exact ⟨es₁ ++ es₂, mor_stop m₁ es₂, (denL_append es₁ es₂).symm⟩

theorem opP_mem {I : Iface} {i : Instr} {h₁ : Nat} {o : Option Nat} {g : PHom H Cfg ResP}
    (hg : g ∈ DenMor Γ I (some h₁))
    (hi : flatChkE (ehExt Γ.tags) Γ.funcs I.env.mi I.env.nl I.env.ret I.env.labels h₁ i = some o) :
    opP i g ∈ DenMor Γ I o := by
  obtain ⟨args, m, rfl⟩ := hg
  exact ⟨[.op i args], mor_op m hi, by rw [denL_singleton, denT_op]⟩

theorem opP_stop_mem {I : Iface} {i : Instr} {g : PHom H Cfg ResP} (hg : g ∈ DenMor Γ I none) :
    opP i g ∈ DenMor Γ I none := by
  obtain ⟨args, m, rfl⟩ := hg
  exact ⟨[.op i args], mor_op_stop m, by rw [denL_singleton, denT_op]⟩

theorem blockP_mem {I : Iface} {bt : BlockType} {np nr : Nat} {o : Option Nat}
    {g : PHom H Cfg ResP} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hg : g ∈ DenMor Γ ⟨I.env.push nr, np⟩ o) (he : endsAt (some o) nr = true) :
    blockP bt g ∈ DenMor Γ I (some (I.h - np + nr)) := by
  obtain ⟨body, m, rfl⟩ := hg
  exact ⟨[.block bt body], mor_block hbt hle m he, by rw [denL_singleton, denT_block]⟩

theorem loopP_mem {I : Iface} {bt : BlockType} {np nr : Nat} {o : Option Nat}
    {g : PHom H Cfg ResP} (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hg : g ∈ DenMor Γ ⟨I.env.push np, np⟩ o) (he : endsAt (some o) nr = true) :
    loopP bt g ∈ DenMor Γ I (some (I.h - np + nr)) := by
  obtain ⟨body, m, rfl⟩ := hg
  exact ⟨[.loop bt body], mor_loop hbt hle m he, by rw [denL_singleton, denT_loop]⟩

theorem ifP_mem {I : Iface} {bt : BlockType} {h₁ np nr : Nat} {ot oe : Option Nat}
    {gc gt ge : PHom H Cfg ResP} (hc : gc ∈ DenMor Γ I (some h₁))
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np + 1 ≤ h₁)
    (ht : gt ∈ DenMor Γ ⟨I.env.push nr, np⟩ ot) (het : endsAt (some ot) nr = true)
    (he : ge ∈ DenMor Γ ⟨I.env.push nr, np⟩ oe) (hee : endsAt (some oe) nr = true) :
    ifP bt gc gt ge ∈ DenMor Γ I (some (h₁ - 1 - np + nr)) := by
  obtain ⟨c, mc, rfl⟩ := hc
  obtain ⟨t, mt, rfl⟩ := ht
  obtain ⟨el, me, rfl⟩ := he
  exact ⟨[.if_ bt c t el], mor_if mc hbt hle mt het me hee, by rw [denL_singleton, denT_if]⟩

theorem ifP_stop_mem {I : Iface} {bt : BlockType} {gc : PHom H Cfg ResP}
    (hc : gc ∈ DenMor Γ I none) (t el : List BExpr) :
    ifP bt gc (denL t) (denL el) ∈ DenMor Γ I none := by
  obtain ⟨c, mc, rfl⟩ := hc
  exact ⟨[.if_ bt c t el], mor_if_stop mc, by rw [denL_singleton, denT_if]⟩

theorem tryP_mem {I : Iface} {bt : BlockType} {cs : List Catch} {ns : List Nat} {np nr : Nat}
    {o : Option Nat} {g : PHom H Cfg ResP}
    (hcs : cs.mapM (clauseCount Γ.tags I.env.mi) = some ns)
    (hbt : blockArity I.env.mi bt = some (np, nr)) (hle : np ≤ I.h)
    (hok : catchOk I.env.labels cs ns = true)
    (hg : g ∈ DenMor Γ ⟨I.env.push nr, np⟩ o) (he : endsAt (some o) nr = true) :
    tryP bt cs g ∈ DenMor Γ I (some (I.h - np + nr)) := by
  obtain ⟨body, m, rfl⟩ := hg
  exact ⟨[.tryTable bt cs body], mor_try hcs hbt hle hok m he, by rw [denL_singleton, denT_try]⟩

theorem seqP_loopP (bt : BlockType) (g g₂ : PHom H Cfg ResP) :
    seqP (loopP bt g) g₂ =
      Silmaril.Elgot.iter (Silmaril.Elgot.mapReturn (loopStepP bt g) (contP g₂)) :=
  Silmaril.Elgot.LawfulElgotMonad.naturality (m := M (CallSig H) H) (loopStepP bt g) (contP g₂)

theorem loopP_uniform (bt : BlockType) (g : PHom H Cfg ResP) {C : Type 1}
    (G : C → M (CallSig H) H (ResP ⊕ C)) (h : Cfg → C)
    (comm : (loopStepP bt g >=> Silmaril.Elgot.liftPure (Sum.map id h)) =
      (Silmaril.Elgot.liftPure h >=> G)) :
    loopP bt g = (Silmaril.Elgot.liftPure h >=> Silmaril.Elgot.iter G) :=
  Silmaril.Elgot.LawfulElgotMonad.uniformity (m := M (CallSig H) H) (loopStepP bt g) G h comm

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct

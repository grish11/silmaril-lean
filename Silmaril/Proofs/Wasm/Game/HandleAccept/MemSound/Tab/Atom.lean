module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Tab.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.AtomsLive
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms
public import Silmaril.Formats.SExp.Api.Thms

/-!
# Proofs: atom tables, n-ary and AST writers

* `tabWrite_atom`, `tabWrite_accept`, `tabAccept_not_write`: what the n-ary table writer decodes
  at a call of an atom import observing `68 69` and at a call of `accept`;
* `tab_atom_sound`, `tab_atom_live`: `atomMod name` through an atom table decoding `68 69` to
  `a` writes exactly the atom `a` (`atom_sat`, `atom_traces`, generic in the roles);
* `tabAstWriterLang_eq`: the AST writer language is the image of the n-ary one under
  `SExp.toAST` (`sexpLang_eq_astLang`), for policies without undefined behaviour.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a : α}

/-! ## The decoder -/

theorem tabAccept_not_write {Op : Type} {ix : TabImports} {o : Callout} {op : Op}
    {args : List (BitVec 32)} {r : BitVec 32} : tabAccept ix o ≠ some (.write op args r) := by
  unfold tabAccept
  split
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

theorem tabAccept_isAccept {Op : Type} {ix : TabImports} {o : Callout} {e : WEv Op (BitVec 32)}
    (h : tabAccept ix o = some e) : ∃ h, e = .accept h := by
  unfold tabAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

theorem tabAccept_acc {Op : Type} (o : Callout) (q : BitVec 32)
    (hi : o.imp = ("sexp", "accept")) (ha : o.args = [.i32 q]) :
    tabAccept (Op := Op) {} o = some (.accept q) := by
  simp [tabAccept, hi, ha, Callout.args1, Callout.i32?, Val.i32]

theorem tabAccept_none {Op : Type} {o : Callout} (h : o.imp ≠ ("sexp", "accept")) :
    tabAccept (Op := Op) {} o = none := by
  simp [tabAccept, h]

theorem tabWrite_atom (hT : T.lookup ("sexp", name) = some (.seg dec))
    (hd : dec [0x68, 0x69] = some a)
    {o : Callout} {w : HostReply} {op : SxOp α} {args : List (BitVec 32)} {r : BitVec 32}
    (hi : o.imp = ("sexp", name)) (hb : o.bytes32 = some [0x68, 0x69])
    (h : tabWrite T {} o w = some (.write op args r)) : op = .atom a ∧ args = [] := by
  unfold tabWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hT, AtomDec.decode, hb, hd, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem tabWrite_atom_eq (hT : T.lookup ("sexp", name) = some (.seg dec))
    (hd : dec [0x68, 0x69] = some a) {o : Callout} {q : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", name)) (hb : o.bytes32 = some [0x68, 0x69]) :
    tabWrite T {} o ⟨.values [.i32 q], mem⟩ = some (.write (.atom a) [] q) := by
  have hr : replyI32 ⟨.values [.i32 q], mem⟩ = some q := rfl
  simp [tabWrite, hr, hi, hT, AtomDec.decode, hb, hd]

theorem tabWrite_accept (hacc : T.lookup ("sexp", "accept") = none) {o : Callout}
    {w : HostReply} (hi : o.imp = ("sexp", "accept")) : tabWrite T {} o w = none := by
  unfold tabWrite
  rcases replyI32 w with _ | r
  · rfl
  · simp [hi, hacc]

/-! ## The module -/

theorem atomOk_of (hn : name ∈ atomNames) : atomOk name = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem atomSpec_of (hn : name ∈ atomNames) :
    (Silmaril.Wasm.Verify.specInstance? (atomMod name)).isSome = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem atomMem_of (hn : name ∈ atomNames) : memSizes (atomMod name) = [65536] := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem accept_ne_of (hn : name ∈ atomNames) : ("sexp", name) ≠ ("sexp", "accept") := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-! ## The n-ary writer -/

/-- **`atomMod name` writes only the atom `a`** through a table decoding `68 69` to `a`. -/
theorem tab_atom_sound (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    tabWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol ⊆ {.atom a} :=
  rolesLang_subset_of_closed (R := tabRoles T {}) (fun _ _ _ _ => tabAccept_not_write)
    (atom_sat P (atomOk_of hn)
      (fun _ hi hb _ _ _ _ hw => let ⟨h1, h2⟩ := tabWrite_atom hT hd hi hb hw; closed_atom h1 h2)
      (fun o hi w _ _ _ hw => by
        change tabWrite T {} o w = _ at hw; rw [tabWrite_accept hacc hi] at hw; cases hw))
    (fun _ _ h => h) ha hw

/-- **`atomMod name` writes the atom `a`**, for every policy. -/
theorem tab_atom_live (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (pol : Policy (BitVec 32)) :
    .atom a ∈ tabWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol :=
  atom_accepts pol a (atom_traces (atomSpec_of hn) (atomMem_of hn) (atomOk_of hn)
    (tabRoles T {}) .enter (fun q => .write (.atom a) [] q) .accept (fun _ => rfl)
    (fun o hi => tabAccept_none (by rw [hi]; exact accept_ne_of hn))
    (fun o q mem hi hb => tabWrite_atom_eq hT hd hi hb)
    tabAccept_acc P (base pol))

/-! ## The AST writer -/

/-- **The AST writer language is the image of the n-ary one** (no undefined behaviour). -/
theorem tabAstWriterLang_eq {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {m : Module} {ix : TabImports} {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    tabAstWriterLang P Envs memIdx m T ix pol =
      SExp.toAST '' tabWriterLang P Envs memIdx m T ix pol :=
  sexpLang_eq_astLang ha hw _

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab

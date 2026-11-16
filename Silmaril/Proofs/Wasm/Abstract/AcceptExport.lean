module

public import Silmaril.Wasm.Abstract.AcceptExport.Defs
public import Silmaril.Wasm.Abstract.AcceptWasm.Thms
public import Silmaril.Wasm.Game.Accept.Export.Thms

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Abstract.AcceptExport

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Abstract Silmaril.Wasm.Abstract.Accept Silmaril.Games.Abstract

variable {P : Profile} {Hosts : Set (HostSemantics Nat)} {m : Module} {name : String}

theorem mem_exportAnswered_iff {w : List UInt8} {r : BitVec 32} :
    w ∈ exportAnswered P Hosts m name r ↔ ∃ e ∈ exportCalls P Hosts m name, e.input = w ∧
      Behaviour.returns [.i32 r] ∈ behRun P e.host {e.store} e.addr e.args := by
  constructor
  · rintro ⟨mt, I, c₀, hi, host, hh, s₀, f₀, hs, a, ma, mt', B₀, B, p, n, ha, hm, hB₀, hseg,
      hov, hb⟩
    exact ⟨⟨host, a, s₀.setMem ma ⟨mt', B⟩, p, n, w⟩,
      ⟨mt, I, c₀, hi, hh, s₀, f₀, hs, ma, mt', B₀, B, ha, hm, hB₀, rfl, hseg, hov⟩, rfl,
      _, rfl, hb⟩
  · rintro ⟨⟨host, a, st, p, n, _⟩, ⟨mt, I, c₀, hi, hh, s₀, f₀, hs, ma, mt', B₀, B, ha, hm, hB₀,
      hst, hseg, hov⟩, rfl, _, rfl, hb⟩
    exact ⟨mt, I, c₀, hi, host, hh, s₀, f₀, hs, a, ma, mt', B₀, B, p, n, ha, hm, hB₀, hseg, hov,
      hst ▸ hb⟩

theorem image_absExportRun (w : List UInt8) :
    endToBehaviour '' absExportRun P Hosts m name w =
      {b | ∃ e ∈ exportCalls P Hosts m name, e.input = w ∧ b ∈ behRun P e.host {e.store} e.addr e.args} := by
  ext b
  constructor
  · rintro ⟨x, ⟨e, he, hw, hx⟩, rfl⟩
    exact ⟨e, he, hw, endRun_wasmFun P e.host {e.store} e.addr e.args ▸ ⟨x, hx, rfl⟩⟩
  · rintro ⟨e, he, hw, hb⟩
    rw [← endRun_wasmFun] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨x, ⟨e, he, hw, hx⟩, rfl⟩

theorem exportRun_eq (w : List UInt8) :
    exportRun P Hosts m name w = {r | ∃ x ∈ absExportRun P Hosts m name w, x ∈ retI32 r} := by
  ext r
  change w ∈ exportAnswered P Hosts m name r ↔ _
  rw [mem_exportAnswered_iff]
  have h := congrArg (Behaviour.returns [.i32 r] ∈ ·) (image_absExportRun (P := P) (Hosts := Hosts)
    (m := m) (name := name) w)
  simp only [Set.mem_image, Set.mem_ofPred_eq] at h
  rw [← h]
  simp [retI32]

theorem mem_acceptsSome_iff {w : List UInt8} {r : BitVec 32} :
    w ∈ Silmaril.Accept.acceptsSome (absExportRun P Hosts m name) (retI32 r) ↔
      r ∈ exportRun P Hosts m name w := by
  rw [exportRun_eq]; rfl

theorem mem_neverRejects_iff {w : List UInt8} {r : BitVec 32} :
    w ∈ Silmaril.Accept.neverRejects (absExportRun P Hosts m name) (retI32 r) ↔
      r ∉ exportRun P Hosts m name w := by
  rw [exportRun_eq]
  exact ⟨fun h ⟨x, hx, hr⟩ => h x hx hr, fun h x hx hr => h ⟨x, hx, hr⟩⟩

end Silmaril.Proofs.Wasm.Abstract.AcceptExport

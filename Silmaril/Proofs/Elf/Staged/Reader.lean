module

public import Silmaril.Elf.Staged.Reader.Defs
public import Silmaril.Elf.Staged.Thms
public import Silmaril.Prelude.Bytes.Thms

/-! # Proofs of `Silmaril.Elf.Staged.Reader`

`fastRead_list` and `sub_kbytes` are the kernel-only part of the KBytes bridge of
hiloopai/silmaril-lean#127 (`Silmaril/Proofs/Elf/Staged/Fast.lean` there), restated over
`Reader.kread`; nothing of #127's native procedures or trust policy is used. -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Staged.Reader

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.X86.Link (Blob)

theorem fastRead_list (l : List UInt8) : ∀ (w o : Nat), o + w ≤ l.length →
    fastRead ⟨⟨l⟩⟩ o w = some (Silmaril.KBytes.leVal ((l.drop o).take w))
  | 0, _, _ => by simp [fastRead, Silmaril.KBytes.leVal]
  | w + 1, o, h => by
    have ho : o < l.length := by omega
    have hs : o < (ByteArray.mk ⟨l⟩).size := by simpa [ByteArray.size] using ho
    simp only [fastRead, hs, ↓reduceDIte]
    rw [fastRead_list l w (o + 1) (by omega)]
    rw [List.drop_eq_getElem_cons ho, List.take_succ_cons]
    simp [Silmaril.KBytes.leVal, ByteArray.getElem_eq_getElem_data]

theorem sub_kbytes {x : Silmaril.KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) : Sub (kread x) (blobOf ⟨raw⟩) := by
  intro o w v hr
  simp only [kread] at hr
  rw [Silmaril.KBytes.readLE_eq x hx] at hr
  split at hr
  · rename_i hle
    cases hr
    apply sub_fast ⟨raw⟩ o w
    show fastRead raw o w = _
    rw [← h]
    exact fastRead_list x.toList w o hle
  · cases hr

theorem sub_window {r : Src} {F : Blob} (hs : Sub r F) (ws : List Span) : Sub (window ws r) F := by
  intro o w v hr
  simp only [window] at hr
  split at hr
  · exact hs o w v hr
  · cases hr

theorem sub_blobRead (F : Blob) : Sub (blobRead F) F := fun _ _ _ h => h

/-- The windowed source of `r` answers as the windowed file. -/
theorem window_mono {r : Src} {F : Blob} (hs : Sub r F) (ws : List Span) :
    ∀ o w v, window ws r o w = some v → window ws (blobRead F) o w = some v := by
  intro o w v hr
  simp only [window] at hr ⊢
  split at hr
  · rename_i hw; simp only [hw, ↓reduceIte]; exact hs o w v hr
  · cases hr

theorem partIs_of_sub {α : Type} {r : Src} {F : Blob} (hs : Sub r F) {ws : List Span}
    {p : Rd α} {v : α} (hc : p.run (window ws r) = some v) : PartIs F ws p v :=
  Rd.run_mono (window_mono hs ws) _ _ hc

end Silmaril.Proofs.Elf.Staged.Reader

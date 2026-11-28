module

public import Silmaril.Semantics.Page.Array.Defs
import Silmaril.Semantics.Page.Trace.Thms

public section
namespace Silmaril.Proofs.Semantics.Page

open Silmaril.Semantics
open Silmaril.Semantics.Page (MapMemory mapStore Store override)
open Silmaril.Semantics.ReadWrite

universe v
variable {Content : Type v} {n : Nat} {trace : Trace Nat Content}

theorem embed_read (a : Page.Array n Content) (page : Nat) :
    (Page.UndefArray.access n Content).read a.embed page = (Page.Array.access n Content).read a page := by
  simp [Page.UndefArray.access, Page.Array.access, Page.Array.embed]

theorem embed_write (a : Page.Array n Content) (page : Nat) (v : Content) :
    (Page.UndefArray.access n Content).write a.embed page v =
      ((Page.Array.access n Content).write a page v).map Page.Array.embed := by
  by_cases h : page < n
  · simp only [Page.UndefArray.access, Page.Array.access, h, dite_true, Option.map_some]
    congr 1
    funext i
    by_cases eq : i = ⟨page, h⟩ <;> simp [Page.Array.embed, override, eq]
  · simp [Page.UndefArray.access, Page.Array.access, h]

theorem embed_injective {a b : Page.Array n Content} (eq : a.embed = b.embed) : a = b := by
  funext i
  exact Option.some.inj (congrFun eq i)

theorem memory_read (a : Page.UndefArray n Content) (page : Nat) :
    (mapStore Nat Content).access.read a.toMemory page = (Page.UndefArray.access n Content).read a page := by
  by_cases h : page < n
  · cases ha : a ⟨page, h⟩ <;>
      simp [Store.access, mapStore, Page.UndefArray.toMemory, Page.UndefArray.access, h, ha, Page.Slot.value]
  · simp [Store.access, mapStore, Page.UndefArray.toMemory, Page.UndefArray.access, h, Page.Slot.value]

theorem memory_write (a : Page.UndefArray n Content) (page : Nat) (v : Content) :
    (mapStore Nat Content).access.write a.toMemory page v =
      ((Page.UndefArray.access n Content).write a page v).map Page.UndefArray.toMemory := by
  by_cases h : page < n
  · have updated : override a.toMemory page (.defined v) =
        Page.UndefArray.toMemory (override a ⟨page, h⟩ (some v)) := by
      funext q
      by_cases eq : q = page
      · subst q
        simp [override, Page.UndefArray.toMemory, h]
      · by_cases hq : q < n
        · have indexNe : (⟨q, hq⟩ : Fin n) ≠ ⟨page, h⟩ := fun neq => eq (congrArg Fin.val neq)
          simp [override, Page.UndefArray.toMemory, hq, eq, indexNe]
        · simp [override, Page.UndefArray.toMemory, hq, eq]
    cases ha : a ⟨page, h⟩ <;>
      simp [Store.access, mapStore, Page.UndefArray.toMemory, Page.UndefArray.access, h, ha, ← updated]
  · simp [Store.access, mapStore, Page.UndefArray.toMemory, Page.UndefArray.access, h]

theorem memory_injective {a b : Page.UndefArray n Content} (eq : a.toMemory = b.toMemory) : a = b := by
  funext i
  have read := congrArg (fun m => (mapStore Nat Content).access.read m i.val) eq
  simpa only [memory_read, Page.UndefArray.access, i.isLt, dite_true] using read

theorem replays_embed_iff {a b : Page.Array n Content} :
    trace.Replays (Page.UndefArray.access n Content) a.embed b.embed ↔
      trace.Replays (Page.Array.access n Content) a b := by
  rw [Trace.replays_map Page.Array.embed embed_read embed_write]
  exact ⟨fun ⟨target, run, eq⟩ => embed_injective eq ▸ run, fun run => ⟨b, run, rfl⟩⟩

theorem replays_memory_iff {a b : Page.UndefArray n Content} :
    trace.Replays (mapStore Nat Content).access a.toMemory b.toMemory ↔
      trace.Replays (Page.UndefArray.access n Content) a b := by
  rw [Trace.replays_map Page.UndefArray.toMemory memory_read memory_write]
  exact ⟨fun ⟨target, run, eq⟩ => memory_injective eq ▸ run, fun run => ⟨b, run, rfl⟩⟩

theorem replays_complete {a b : Page.UndefArray n Content}
    (run : trace.Replays (Page.UndefArray.access n Content) a b) (fill : Page.Array n Content) :
    trace.Replays (Page.Array.access n Content) (a.complete fill) (b.complete fill) := by
  induction trace generalizing a with
  | nil => exact congrArg (fun a => Page.UndefArray.complete a fill) run
  | cons event rest ih =>
    cases event with
    | read p v =>
      obtain ⟨read, tail⟩ := run
      change (Page.Array.access n Content).read (a.complete fill) p = some v ∧ _
      have h : p < n := by
        by_cases h : p < n
        · exact h
        · simp [Page.UndefArray.access, h] at read
      simp only [Page.UndefArray.access, h, dite_true] at read
      exact ⟨by simp [Page.Array.access, Page.UndefArray.complete, h, read], ih tail⟩
    | write p v =>
      obtain ⟨next, write, tail⟩ := run
      have h : p < n := by
        by_cases h : p < n
        · exact h
        · simp [Page.UndefArray.access, h] at write
      simp only [Page.UndefArray.access, h, dite_true, Option.some.injEq] at write
      subst next
      refine ⟨Page.UndefArray.complete (override a ⟨p, h⟩ (some v)) fill, ?_, ih tail⟩
      simp only [Page.Array.access, h, dite_true, Option.some.injEq]
      funext i
      by_cases eq : i = ⟨p, h⟩ <;> simp [override, Page.UndefArray.complete, eq]

theorem satisfiable_iff (fill : Page.Array n Content) :
    Page.UndefArray.Satisfiable n trace ↔ Page.Array.Satisfiable n trace := by
  constructor
  · intro ⟨a, b, run⟩
    exact ⟨a.complete fill, b.complete fill, replays_complete run fill⟩
  · intro ⟨a, b, run⟩
    exact ⟨a.embed, b.embed, replays_embed_iff.mpr run⟩

theorem undef_replay_inBounds {a b : Page.UndefArray n Content}
    (run : trace.Replays (Page.UndefArray.access n Content) a b) : Page.Array.InBounds n trace := by
  induction trace generalizing a with
  | nil => simp [Page.Array.InBounds, Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes]
  | cons event rest ih =>
    intro page touches
    have touches' := (Trace.footprint_append (first := [event]) (last := rest)).mp touches
    cases event with
    | read p v =>
      have pBound : p < n := by
        by_cases h : p < n
        · exact h
        · have read := run.1
          simp [Page.UndefArray.access, h] at read
      rcases touches' with single | tail
      · have eq : page = p := by
          simpa [Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes] using single
        exact eq ▸ pBound
      · exact ih run.2 page tail
    | write p v =>
      obtain ⟨next, write, tailRun⟩ := run
      have pBound : p < n := by
        by_cases h : p < n
        · exact h
        · simp [Page.UndefArray.access, h] at write
      rcases touches' with single | tail
      · have eq : page = p := by
          simpa [Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes] using single
        exact eq ▸ pBound
      · exact ih tailRun page tail

end Silmaril.Proofs.Semantics.Page

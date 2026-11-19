module
public import Silmaril.Elf.Corpus.CjsonArrayItem.Context.Defs
/-! Regression lemmas concern only the declared observation, not refinement.
`after` is arbitrary: legitimate changes to private allocation bookkeeping cannot
mask any caller mutation. No field is normalized in these rejection checks. -/
open Silmaril.Cerberus Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonArrayItem

example (i : Context.Input) (before after : Mem.Concrete.State)
    (id : Int) (lower : 0 ≤ id) (upper : id < i.length.val+4)
    (changed : before.allocations.lookup id ≠ after.allocations.lookup id) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed ((h.2.2.2.1 id lower upper).1)

example (i : Context.Input) (before after : Mem.Concrete.State)
    (id : Int) (lower : 0 ≤ id) (upper : id < i.length.val+4)
    (changed : ¬ (id ∈ before.dead ↔ id ∈ after.dead)) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed ((h.2.2.2.1 id lower upper).2)

example (i : Context.Input) (before after : Mem.Concrete.State)
    (off : Nat) (bound : off < (i.length.val+2)*64)
    (changed : before.pointerBytes.lookup ((i.base+off : Nat) : Int) ≠
      after.pointerBytes.lookup ((i.base+off : Nat) : Int)) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed ((h.2.2.2.2.1 off bound).2)

example (i : Context.Input) (before after : Mem.Concrete.State)
    (off : Nat) (bound : off < (i.length.val+2)*64)
    (changed : before.bytes.lookup ((i.base+off : Nat) : Int) ≠
      after.bytes.lookup ((i.base+off : Nat) : Int)) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed ((h.2.2.2.2.1 off bound).1)

example (i : Context.Input) (before after : Mem.Concrete.State)
    (changed : before.stdout ≠ after.stdout) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed h.2.2.1

-- A freshly allocated private object can be dead and still must not escape.
example (i : Context.Input) (id address : Int) (privateId : i.length.val+4 ≤ id) :
    Context.pointerWord i (.loaded (.specified (.pointer (.allocated id address)))) = none := by
  simp only [Context.pointerWord]
  have h : ¬ id < (i.length.val : Int)+4 := by omega
  simp [h]

example (i : Context.Input) (before after : Mem.Concrete.State)
    (id : Int) (fresh : before.nextId ≤ id) (allocated : id < after.nextId)
    (live : id ∉ after.dead) : ¬ Context.callerPreserved i before after := by
  intro h
  exact live (h.2.2.2.2.2.2 id fresh allocated)

example (i : Context.Input) (before after : Mem.Concrete.State)
    (off : Int) (bound : off < 12)
    (changed : before.bytes.lookup (4096+off) ≠ after.bytes.lookup (4096+off)) :
    ¬ Context.callerPreserved i before after := by
  intro h
  exact changed ((h.2.2.2.2.2.1 off bound).1)

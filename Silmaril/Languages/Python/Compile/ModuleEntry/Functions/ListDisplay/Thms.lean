module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ListDisplay.Defs
public import Silmaril.Languages.Python.Core.Module.ListObject.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ListDisplay

open Source (Name)
open Core.Module (ListHeap Value)

theorem Display.prepare_allocated {error : Type} (display : Display)
    (read : Name → Except error Value) (heap : ListHeap) (contents : List Value)
    (evaluated : display.items.mapM (Item.eval read) = .ok contents) :
    display.prepare read heap = (.ok (heap.allocate contents).1, (heap.allocate contents).2) := by
  simp [prepare, evaluated]

theorem Display.prepare_lookup {error : Type} (display : Display)
    (read : Name → Except error Value) (heap : ListHeap) (contents : List Value)
    (evaluated : display.items.mapM (Item.eval read) = .ok contents) :
    (display.prepare read heap).2.lookup heap.objects.size = some contents := by
  rw [display.prepare_allocated read heap contents evaluated]
  exact (ListHeap.allocate_lookup_new heap contents).2

theorem Display.prepare_firstError {error : Type} (read : Name → Except error Value)
    (heap : ListHeap) (prefixItems tail : List Item) (item : Item) (negated : Bool)
    (contents : List Value) (failure : error)
    (earlier : prefixItems.mapM (Item.eval read) = .ok contents)
    (failed : item.eval read = .error failure) :
    (Display.mk (prefixItems ++ item :: tail) negated).prepare read heap = (.error failure, heap) := by
  simp [prepare, earlier, failed]
  rfl

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ListDisplay

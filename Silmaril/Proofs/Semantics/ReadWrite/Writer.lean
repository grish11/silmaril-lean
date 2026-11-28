module

public import Silmaril.Semantics.ReadWrite.Writer.Defs
public import Cslib.Foundations.Control.Monad.IsMonadHom

public section
namespace Silmaril.Proofs.Semantics.ReadWrite.Writer

open Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v}

theorem eraseValues_reads :
    (AddressLog.reads.comp ValueLog.eraseValues : ValueLog Address Value →* AddressListLog Address) =
      EntryLog.eraseValues.comp ValueLog.reads := by
  apply MonoidHom.ext
  intro log
  exact congrArg FreeMonoid.ofList (Trace.eraseValues_reads log.toList)

theorem eraseValues_writes :
    (AddressLog.writes.comp ValueLog.eraseValues : ValueLog Address Value →* AddressListLog Address) =
      EntryLog.eraseValues.comp ValueLog.writes := by
  apply MonoidHom.ext
  intro log
  exact congrArg FreeMonoid.ofList (Trace.eraseValues_writes log.toList)

theorem useDef_defs :
    (UseDef.defsLog.comp AddressLog.useDef : AddressLog Address →* AddressSet Address) =
      AccessSets.defsLog.comp AddressLog.accessSets := by
  apply FreeMonoid.hom_eq
  intro event
  cases event <;> simp [AddressLog.useDef, UseDef.defsLog, AccessSets.defsLog, AddressLog.accessSets,
    AddressTrace.accessSets, AddressTrace.writes, AccessSets.defs, AddressEvent.useDef]

theorem useDef_footprint :
    (UseDef.footprintLog.comp AddressLog.useDef : AddressLog Address →* AddressSet Address) =
      AccessSets.footprintLog.comp AddressLog.accessSets := by
  apply FreeMonoid.hom_eq
  intro event
  cases event <;> simp [AddressLog.useDef, UseDef.footprintLog, AccessSets.footprintLog, AddressLog.accessSets,
    AddressTrace.accessSets, AddressTrace.reads, AddressTrace.writes, UseDef.footprint,
    AccessSets.footprint, AddressEvent.useDef]

variable {First Second Third : Type u} [Monoid First] [Monoid Second] [Monoid Third]
variable {m : Type u → Type w} [Monad m] [LawfulMonad m] {α β : Type u}

theorem mapLog_bind (f : First →* Second) (x : WriterT First m α) (k : α → WriterT First m β) :
    WriterLog.mapLog f (x >>= k) = WriterLog.mapLog f x >>= fun a => WriterLog.mapLog f (k a) := by
  apply WriterT.ext
  change (Prod.map id f <$> (x.run >>= fun (a, first) =>
    (fun (b, last) => (b, first * last)) <$> (k a).run)) =
      ((Prod.map id f <$> x.run) >>= fun (a, first) =>
        (fun (b, last) => (b, first * last)) <$> (Prod.map id f <$> (k a).run))
  simp only [map_bind, bind_map_left, Functor.map_map]
  congr 1
  funext pair
  rcases pair with ⟨a, first⟩
  congr 1
  funext pair
  rcases pair with ⟨b, last⟩
  simp

end Silmaril.Proofs.Semantics.ReadWrite.Writer

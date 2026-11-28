module

public import Silmaril.Semantics.ReadWrite.Writer.Defs
public import Cslib.Foundations.Control.Monad.IsMonadHom
import Silmaril.Proofs.Semantics.ReadWrite.Writer

public section
namespace Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v}

@[simp] theorem ValueLog.eraseValues_toLog (trace : Trace Address Value) :
    eraseValues trace.toLog = trace.eraseValues.toLog := rfl

@[simp] theorem ValueLog.reads_toLog (trace : Trace Address Value) :
    (reads trace.toLog).toList = trace.reads := rfl

@[simp] theorem ValueLog.writes_toLog (trace : Trace Address Value) :
    (writes trace.toLog).toList = trace.writes := rfl

@[simp] theorem ValueLog.accessSets_toLog (trace : Trace Address Value) :
    accessSets trace.toLog = trace.accessSets := trace.accessSets_eraseValues

@[simp] theorem ValueLog.useDef_toLog (trace : Trace Address Value) :
    useDef trace.toLog = trace.useDef := trace.useDef_eraseValues

theorem ValueLog.eraseValues_reads :
    (AddressLog.reads.comp eraseValues : ValueLog Address Value →* AddressListLog Address) =
      EntryLog.eraseValues.comp reads :=
  Proofs.Semantics.ReadWrite.Writer.eraseValues_reads

theorem ValueLog.eraseValues_writes :
    (AddressLog.writes.comp eraseValues : ValueLog Address Value →* AddressListLog Address) =
      EntryLog.eraseValues.comp writes :=
  Proofs.Semantics.ReadWrite.Writer.eraseValues_writes

theorem AddressLog.accessSets_reads :
    (AccessSets.readsLog.comp accessSets : AddressLog Address →* AddressSet Address) =
      AddressListLog.toSet.comp reads :=
  MonoidHom.ext fun _ => rfl

theorem AddressLog.accessSets_defs :
    (AccessSets.defsLog.comp accessSets : AddressLog Address →* AddressSet Address) =
      AddressListLog.toSet.comp writes :=
  MonoidHom.ext fun _ => rfl

theorem AddressLog.useDef_defs :
    (UseDef.defsLog.comp useDef : AddressLog Address →* AddressSet Address) =
      AccessSets.defsLog.comp accessSets :=
  Proofs.Semantics.ReadWrite.Writer.useDef_defs

theorem AddressLog.useDef_footprint :
    (UseDef.footprintLog.comp useDef : AddressLog Address →* AddressSet Address) =
      AccessSets.footprintLog.comp accessSets :=
  Proofs.Semantics.ReadWrite.Writer.useDef_footprint

namespace WriterLog

variable {First Second Third : Type u} [Monoid First] [Monoid Second] [Monoid Third]
variable {m : Type u → Type w} [Monad m] [LawfulMonad m] {α β : Type u}

@[simp] theorem mapLog_pure (f : First →* Second) (a : α) :
    mapLog f (pure a : WriterT First m α) = pure a := by
  apply WriterT.ext
  change (Prod.map id f <$> (pure (a, 1) : m (α × First))) = pure (a, 1)
  simp

@[simp] theorem mapLog_bind (f : First →* Second) (x : WriterT First m α) (k : α → WriterT First m β) :
    mapLog f (x >>= k) = mapLog f x >>= fun a => mapLog f (k a) :=
  Proofs.Semantics.ReadWrite.Writer.mapLog_bind f x k

theorem isMonadHom (f : First →* Second) :
    Cslib.IsMonadHom (WriterT First m) (WriterT Second m) (mapLog f) :=
  .mk' (mapLog_pure f) (mapLog_bind f)

@[simp] theorem mapLog_tell (f : First →* Second) (log : First) :
    mapLog f (tell log : WriterT First m PUnit) = tell (f log) := by
  apply WriterT.ext
  change (Prod.map id f <$> (pure (⟨⟩, log) : m (PUnit × First))) = pure (⟨⟩, f log)
  simp

@[simp] theorem mapLog_id (x : WriterT First m α) : mapLog (MonoidHom.id First) x = x := by
  apply WriterT.ext
  change id <$> x.run = x.run
  exact id_map _

@[simp] theorem mapLog_comp (g : Second →* Third) (f : First →* Second) (x : WriterT First m α) :
    mapLog (g.comp f) x = mapLog g (mapLog f x) := by
  apply WriterT.ext
  change Prod.map id (g.comp f) <$> x.run = Prod.map id g <$> (Prod.map id f <$> x.run)
  rw [Functor.map_map]
  rfl

/-- A commuting pair of paths between log monoids also commutes between their Writers. -/
theorem mapLog_square {Other : Type u} [Monoid Other] {f : First →* Second} {g : Second →* Third}
    {h : First →* Other} {k : Other →* Third} (square : g.comp f = k.comp h) (x : WriterT First m α) :
    mapLog g (mapLog f x) = mapLog k (mapLog h x) := by
  rw [← mapLog_comp, ← mapLog_comp, square]

variable {Address Value : Type u}

theorem mapLog_accessSets (x : WriterT (ValueLog Address Value) m α) :
    mapLog AddressLog.accessSets (mapLog ValueLog.eraseValues x) = mapLog ValueLog.accessSets x :=
  (mapLog_comp _ _ x).symm

theorem mapLog_useDef (x : WriterT (ValueLog Address Value) m α) :
    mapLog AddressLog.useDef (mapLog ValueLog.eraseValues x) = mapLog ValueLog.useDef x :=
  (mapLog_comp _ _ x).symm

theorem mapLog_eraseValues_reads (x : WriterT (ValueLog Address Value) m α) :
    mapLog AddressLog.reads (mapLog ValueLog.eraseValues x) =
      mapLog EntryLog.eraseValues (mapLog ValueLog.reads x) :=
  mapLog_square ValueLog.eraseValues_reads x

theorem mapLog_eraseValues_writes (x : WriterT (ValueLog Address Value) m α) :
    mapLog AddressLog.writes (mapLog ValueLog.eraseValues x) =
      mapLog EntryLog.eraseValues (mapLog ValueLog.writes x) :=
  mapLog_square ValueLog.eraseValues_writes x

theorem mapLog_accessSets_reads (x : WriterT (AddressLog Address) m α) :
    mapLog AccessSets.readsLog (mapLog AddressLog.accessSets x) =
      mapLog AddressListLog.toSet (mapLog AddressLog.reads x) :=
  mapLog_square AddressLog.accessSets_reads x

theorem mapLog_accessSets_defs (x : WriterT (AddressLog Address) m α) :
    mapLog AccessSets.defsLog (mapLog AddressLog.accessSets x) =
      mapLog AddressListLog.toSet (mapLog AddressLog.writes x) :=
  mapLog_square AddressLog.accessSets_defs x

theorem mapLog_useDef_defs (x : WriterT (AddressLog Address) m α) :
    mapLog UseDef.defsLog (mapLog AddressLog.useDef x) =
      mapLog AccessSets.defsLog (mapLog AddressLog.accessSets x) :=
  mapLog_square AddressLog.useDef_defs x

theorem mapLog_useDef_footprint (x : WriterT (AddressLog Address) m α) :
    mapLog UseDef.footprintLog (mapLog AddressLog.useDef x) =
      mapLog AccessSets.footprintLog (mapLog AddressLog.accessSets x) :=
  mapLog_square AddressLog.useDef_footprint x

end WriterLog

@[simp] theorem Trace.record_nil {Address Value Result : Type u} (result : Result) :
    Trace.record ([] : Trace Address Value) result = pure result := rfl

theorem Trace.record_bind {Address Value α β : Type u} (first : Trace Address Value) (a : α)
    (next : α → Trace Address Value) (result : α → β) :
    (first.record a >>= fun a' => (next a').record (result a')) =
      (first ++ next a).record (result a) := rfl

end Silmaril.Semantics.ReadWrite

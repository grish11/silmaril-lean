module

public import Silmaril.Semantics.Brookes.StoreEquiv.Defs
public import Silmaril.Semantics.Brookes.Thms
import Silmaril.Proofs.Semantics.Brookes.StoreEquiv

public section

namespace Silmaril.Semantics.Brookes

variable {S T A B : Type*}

@[simp] theorem Trace.mapStores_inverse (e : S ≃ T) (word : Trace S) :
    Trace.mapStores e.symm (Trace.mapStores e word) = word :=
  Proofs.Semantics.Brookes.StoreEquiv.mapStores_inverse e word

theorem Reduces.mapStores (f : S → T) {source target : Trace S} (h : Reduces source target) :
    Reduces (Trace.mapStores f source) (Trace.mapStores f target) :=
  Proofs.Semantics.Brookes.StoreEquiv.reduces_mapStores f h

/-- Transport reflects as well as preserves arbitrary completed words. -/
theorem Behavior.transport_accepts_iff (e : S ≃ T) (b : Behavior S A)
    (word : Trace T) (result : A) :
    (b.transport e).accepts word result ↔ b.accepts (Trace.mapStores e.symm word) result :=
  Proofs.Semantics.Brookes.StoreEquiv.transport_accepts_iff e b word result

theorem Behavior.transport_atomic (e : S ≃ T) (step : S → S → A → Prop) :
    (Behavior.atomic step).transport e =
      Behavior.atomic (fun s t a => step (e.symm s) (e.symm t) a) :=
  Proofs.Semantics.Brookes.StoreEquiv.transport_atomic e step

theorem Behavior.transport_ret (e : S ≃ T) (value : A) :
    (Behavior.ret value).transport e = Behavior.ret value := by
  rw [ret, transport_atomic, ret]
  simp only [Equiv.apply_eq_iff_eq]

theorem Behavior.transport_bind (e : S ≃ T) (first : Behavior S A) (next : A → Behavior S B) :
    (first.bind next).transport e =
      (first.transport e).bind (fun a => (next a).transport e) :=
  Proofs.Semantics.Brookes.StoreEquiv.transport_bind e first next

theorem Behavior.transport_completes_iff (e : S ≃ T) (b : Behavior S A) (s t : S) (result : A) :
    (b.transport e).completes (e s) (e t) result ↔ b.completes s t result := by
  simpa only [completes, Trace.mapStores, List.map_cons, List.map_nil, Equiv.symm_apply_apply] using
    transport_accepts_iff e b [(e s, e t)] result

end Silmaril.Semantics.Brookes

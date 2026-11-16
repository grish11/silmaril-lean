module

public import Silmaril.Logic.Egglog.Core.Derivation
public import Silmaril.Logic.Egglog.Core.Prolog
public import Silmaril.Logic.Egglog.Core.FirstOrder
public import Silmaril.Logic.Egglog.Core.Graph.Thms
import Silmaril.Proofs.Logic.Egglog.Sound

@[expose] public section

namespace Silmaril.Logic.Egglog.Core

theorem derivation_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {facts : Set (Atom S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hfacts : StateHolds M ρ facts) {a : Atom S Δ} (d : Derivation rules facts a) : a.Holds M ρ :=
  Silmaril.Proofs.Logic.Egglog.derivation_sound M ρ hrules hfacts d

theorem insertStep_sound {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    {rules : Set (Rule S)} {before after : Set (Atom S Δ)} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (hrules : ∀ r ∈ rules, r.Holds M)
    (hbefore : StateHolds M ρ before) (step : InsertStep rules before after) : StateHolds M ρ after :=
  Silmaril.Proofs.Logic.Egglog.insertStep_sound M ρ hrules hbefore step

def Defined {S : Signature} (M : Model S) {n w s} (f : S.Function n w s)
    (args : ∀ i, M.carrier (w i)) : Prop := ∃ value, M.row f args value

theorem lookup_unique {S : Signature} (M : Model S) {n w s} (f : S.Function n w s)
    (args : ∀ i, M.carrier (w i)) {x y} (hx : M.row f args x) (hy : M.row f args y) : x = y :=
  M.functional f args x y hx hy

end Silmaril.Logic.Egglog.Core

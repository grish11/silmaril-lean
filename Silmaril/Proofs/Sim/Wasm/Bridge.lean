module

public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Sim.Institution.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Proofs: Wasm-level judgements give sound simulators

Names are in `Silmaril.Sim.Wasm.ExportSim`, exported by `Silmaril/Sim/Wasm/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Wasm.ExportSim

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)

variable {C L V H : Type} {K : ExportSim C L V H} {B : Machine C L V}
  {R : Store H → B.St → Prop} {c : C}

/-- Per-method soundness from one every-run triple per ghost reference state. -/
theorem methodOK_of_fspecValid
    (h : ∀ b, FSpecValid K.P K.host (K.addr c) (K.methodSpec B R c b)) : K.MethodOK B R c :=
  fun b _ _ _ res hR hok hs =>
    Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals (h b) ⟨rfl, hR⟩ hs res rfl hok

/-- Per-method soundness from the ghost-free triple. -/
theorem methodOK_of_fspecValidU (h : FSpecValid K.P K.host (K.addr c) (K.methodSpecU B R c)) :
    K.MethodOK B R c :=
  fun b _ _ _ res hR hok hs =>
    Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals h ⟨rfl, b, hR⟩ hs res rfl hok b hR

/-- **Same-module accessors (code substitution by contracts).** The methods' specifications
`Γe` are valid relative to the accessor specifications `Γi` over the closed-world semantics
(`Hoare.CtxSat`: the core proof uses the accessors only through `Γi`, never their code), and
`Γi` is valid for this module's accessor bodies. A representation (G or M) only changes the
accessor bodies and `Γi`; a core proof parametric in the representation serves both. -/
theorem methodOK_of_ctxSat {Γi Γe : Silmaril.Wasm.Logic.Hoare.Ctx H}
    (hm : Silmaril.Wasm.Logic.Hoare.CtxSat K.P K.host Γi Γe)
    (hi : Silmaril.Wasm.Logic.Hoare.Ctx.Valid K.P K.host Γi)
    (hΓ : Γe (K.addr c) = some (K.methodSpecU B R c)) : K.MethodOK B R c :=
  fun b _ _ _ res hR hok hs =>
    Silmaril.Wasm.Logic.Hoare.ctxSat_invoke_sound hm hi hΓ ⟨rfl, b, hR⟩ hs res rfl hok b hR

/-- Validity of a context from one every-run triple per address (one problem per accessor). -/
theorem ctx_valid_of_each {Γ : Silmaril.Wasm.Logic.Hoare.Ctx H} (as : List Nat)
    (hdom : ∀ a S, Γ a = some S → a ∈ as)
    (h : ∀ a ∈ as, ∀ S, Γ a = some S → FSpecValid K.P K.host a S) :
    Silmaril.Wasm.Logic.Hoare.Ctx.Valid K.P K.host Γ :=
  fun n a S hS => h a (hdom a S hS) S hS n

/-- **A certified Wasm simulator is a simulation** of its machine by the reference. -/
def Cert.simulation (Ct : K.Cert B) : Simulation K.toMachine B :=
  Simulation.ofMethods Ct.R Ct.view_le Ct.load fun c b a a' hR hcall => by
    obtain ⟨f', res, hok, hs⟩ := hcall
    exact Ct.method c b a a' f' res hR hok hs

/-- A certificate gives the obligations of the derived `WasmSim` form. -/
def Cert.obligations (Ct : K.Cert B) : K.toWasmSim.Obligations B where
  R := Ct.R
  view_le := Ct.view_le
  load := Ct.load
  method c b a a' hR hcall := by
    obtain ⟨f', res, hok, hs⟩ := hcall
    exact Ct.method c b a a' f' res hR hok hs

/-- **A certified Wasm simulator is sound.** -/
theorem Cert.sound (Ct : K.Cert B) : Silmaril.Sim.Sound K.toWasmSim.toMachine B :=
  ⟨Ct.simulation⟩

/-- **Soundness of a Core 3 simulator → independent Wasm problems**: the view condition, the
loading condition, and one per-method problem per command (each discharged by
`methodOK_of_fspecValid`, `methodOK_of_vc` or `methodOK_of_moduleSat`). -/
def reduction (K : ExportSim C L V H) (B : Machine C L V) (R : Store H → B.St → Prop)
    (cs : List C) (hcs : ∀ c, c ∈ cs) :
    Silmaril.Sim.Institution.Reduction (Silmaril.Sim.Sound K.toWasmSim.toMachine B) where
  subgoals := (∀ a b, R a b → PState.Le (K.get a) (B.view b)) ::
    (∀ b, ∃ a, R a b ∧ K.get a = B.view b) :: cs.map (K.MethodOK B R)
  sound h :=
    Cert.sound (K := K)
      { R := R
        view_le := fun {a b} hab => h _ (List.mem_cons_self ..) a b hab
        load := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        method := fun c => h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.2 ⟨c, hcs c, rfl⟩))) }

/-- **Soundness of a representation → a shared core problem + one problem per accessor**
(+ view, loading). `Γi`, `Γe` are this representation's instances of the core's
representation-parametric contexts; `as` are the accessor addresses. -/
def reductionCore (K : ExportSim C L V H) (B : Machine C L V) (R : Store H → B.St → Prop)
    (Γi Γe : Silmaril.Wasm.Logic.Hoare.Ctx H) (as : List Nat) (hdom : ∀ a S, Γi a = some S → a ∈ as)
    (hΓ : ∀ c, Γe (K.addr c) = some (K.methodSpecU B R c)) :
    Silmaril.Sim.Institution.Reduction (Silmaril.Sim.Sound K.toWasmSim.toMachine B) where
  subgoals := (∀ a b, R a b → PState.Le (K.get a) (B.view b)) ::
    (∀ b, ∃ a, R a b ∧ K.get a = B.view b) ::
    Silmaril.Wasm.Logic.Hoare.CtxSat K.P K.host Γi Γe ::
    as.map fun a => ∀ S, Γi a = some S → FSpecValid K.P K.host a S
  sound h := by
    have hv := h _ (List.mem_cons_self ..)
    have hl := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hm := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hi : Silmaril.Wasm.Logic.Hoare.Ctx.Valid K.P K.host Γi :=
      ctx_valid_of_each (K := K) as hdom fun a ha => h _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩))))
    exact Cert.sound (K := K)
      { R := R
        view_le := fun {a b} hab => hv a b hab
        load := hl
        method := fun c => methodOK_of_ctxSat hm hi (hΓ c) }

end Silmaril.Sim.Wasm.ExportSim

end

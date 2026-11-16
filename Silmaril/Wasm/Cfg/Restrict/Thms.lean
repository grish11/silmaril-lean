module

public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
import Silmaril.Proofs.Wasm.Cfg.Restrict

@[expose] public section

/-!
# Host-free runs keep the store's functions

Without a host (`fun _ _ _ _ => False`), Core steps never change the store's function list, so a
region or machine run keeps the whole list `F` of its start (not only the function names: the
function instances, with their types, modules and code), provided the oracle's answers keep it.
Every call is then made from a store with `F`, and so is every check that reads only `F`, such
as `Interp.StoreChkE`. An oracle `C` can be replaced by any `C'` that agrees with it on stores
with `F`, in runs, steps, infinite runs, `MDivC` and `MDivT`.

This is stated for the host-free semantics only. A host call may change the store, and nothing
here applies to host-mutated stores.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {C C' : Abstract.CallRel H} {F : List (FuncInst H)}

/-- **A host-free region run keeps the store's function list `F`, and only calls from stores
with it.** -/
theorem runC_funcs
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Region.Out}
    (h : Region.RunC P (fun _ _ _ _ => False) C s f vs code s' f' o) (hI : s.funcs = F) :
    Region.RunC P (fun _ _ _ _ => False) C' s f vs code s' f' o ∧ s'.funcs = F :=
  Proofs.Region.runC_funcs hC h hI

/-- **A host-free machine step keeps the store's function list `F`.** -/
theorem mstepC_funcs
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {body : Expr} {st st' : MState H} (h : MStepC P (fun _ _ _ _ => False) C body st st')
    (hI : st.store.funcs = F) :
    MStepC P (fun _ _ _ _ => False) C' body st st' ∧ st'.store.funcs = F :=
  Proofs.Region.mstepC_funcs hC h hI

/-- **Host-free machine divergence transfers between oracles agreeing on stores with `F`.** -/
theorem mdivC_funcs
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : MDivC P (fun _ _ _ _ => False) C D body st) (hI : st.store.funcs = F) :
    MDivC P (fun _ _ _ _ => False) C' D body st :=
  Proofs.Region.mdivC_funcs hC h hI

/-- **Host-free frame divergence transfers between oracles agreeing on stores with `F`.** -/
theorem mdivT_funcs
    (hC : ∀ s a us out, s.funcs = F → C s a us out → C' s a us out ∧ out.1.funcs = F)
    {D : Store H → Nat → List Val → Prop} {body : Expr} {st : MState H}
    (h : MDivT P (fun _ _ _ _ => False) C D body st) (hI : st.store.funcs = F) :
    MDivT P (fun _ _ _ _ => False) C' D body st :=
  Proofs.Region.mdivT_funcs hC h hI

end Silmaril.Wasm.Cfg.Machine

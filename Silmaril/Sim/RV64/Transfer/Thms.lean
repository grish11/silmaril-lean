module

public import Silmaril.Proofs.Sim.RV64.Transfer.Absdiff
public import Silmaril.Proofs.Sim.RV64.Transfer.Max3
public import Silmaril.Proofs.Sim.RV64.Transfer.Clamp
public import Silmaril.Proofs.Sim.RV64.Transfer.Sq
public import Silmaril.Proofs.Sim.RV64.Transfer.SumTo
public import Silmaril.Proofs.Sim.RV64.Transfer.Gcdu

/-!
# RV64 problems of the RV64 reduction plans, transported from their Wasm problems: results

Generic part (`Silmaril.Proofs.Sim.RV64.Transfer.Generic`, proved once):

* **`fnISA_of_wasm`**: a symbolic tree `T` of the words (`extSym … = some T`, checked by
  `decide`, sound by `Silmaril.Sim.RV64.Sym.extSym_sound`), a run of the instantiated Wasm function
  satisfying the contract (the Wasm problem), and translation validation (every run returns
  `T.eval σ`) give the RV64 problem `FnISA` against `Silmaril.RiscV.Ext.MState.step` on the
  actual words, including the leaf ABI (`ra`, `sp`, `s0`–`s11`);
* `tv_of_body` (translation validation from one `wpc` condition `BodyTV`, closed by the tactic
  `rv_tv`), `run_of_wp` (a run from an entry's `Spec`), `wp_of_body` (an entry's `Spec` from
  `BodyTV`).

Per function (`Absdiff`, `Max3`, `Clamp`, `Sq`; generated files, 4–7 s each): `sym` (`decide`),
`body` (`rv_tv`), `isa : Spec → ISA` (the transfer), `spec_tv : Spec` and `isa_solved : ISA`.

Loops (`SumTo`): cut points (`Silmaril.Sim.RV64.Cfg`, `cfgSym`/`reach_block`, proved once); the
translation validation is `wpc` with the simulation invariant `Reach` at the Wasm loop (every
returning Wasm run is an RV64 return); termination comes from the Wasm problem (`Spec` is total;
`spec_tactic` uses the plan's invariant and the measure `a0`). `SumTo.isa_solved : ISA` with
`FnISAP` (contract with precondition + leaf ABI).

`Gcdu`: loop + call: translation validation with the modular call rule of
`Silmaril.Wasm.Logic.Hoare` (spec context `Γr` with the helper's `remuSpec`); the Wasm problem `SpecInst` (in the instantiated module) solved with the
plan's invariant and measure `a1`; `Gcdu.isa_solved`. The generated `Rv64Gcdu.Spec` quantifies over every
module instance, where the call is unconstrained, so it is not used.

Not covered: memory accesses.
-/

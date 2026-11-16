module

public import Silmaril.Wasm.Logic.Hoare.WasmAdd.Thms

@[expose] public section
namespace Silmaril.Logic.Hoare.Wasm

/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_hwp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_hwp
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_exec
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_steps
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_valid
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_reachability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_reachability
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_matching
/-- info: 'Silmaril.Logic.Hoare.Wasm.addBlock_false_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addBlock_false_matching
/-- info: 'Silmaril.Logic.Hoare.Wasm.wrapping_add_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrapping_add_exec
/-- info: 'Silmaril.Logic.Hoare.Wasm.wrapping_add_wrong_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrapping_add_wrong_post

end Silmaril.Logic.Hoare.Wasm

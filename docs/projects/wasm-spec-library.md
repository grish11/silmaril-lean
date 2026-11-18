# Wasm specification library

`Silmaril/WasmSpec` holds small WebAssembly programs, each with a Lean specification and
machine-checked solutions, one directory per entry. The [Wasm catalogue](wasm-catalog.md) lists
them next to the other verified Wasm artifacts.

**What is verified.** Each program is WAT text, quoted into a Core 3.0 `Module` value by
`wat3!`. The theorems are about that module under the Core 3.0 small-step semantics, at every
numeric profile and host relation unless the entry says otherwise. They are not about a separately
compiled `.wasm` file. `scripts/check-wasm-spec.py` (run by `make check`) checks that the quoted
text equals the `.wat` file beside it.

| Entry | Version | Program | Specification | Solutions |
| --- | --- | --- | --- | --- |
| [Adder](../../Silmaril/WasmSpec/Adder/manifest.toml) | 1.0.0 | `add x y` | `x + y` (mod 2^32) | tactic, tactic+script |
| [Add3](../../Silmaril/WasmSpec/Add3/manifest.toml) | 1.0.0 | `add (add x y) z` via an imported adder | `x + y + z`, for every adder meeting `Adder.CallSpec` | tactic |
| [Abs](../../Silmaril/WasmSpec/Abs/manifest.toml) | 1.0.0 | branch-free `(x ^ m) - m` | wrapping absolute value | tactic |
| [Max](../../Silmaril/WasmSpec/Max/manifest.toml) | 1.0.0 | `if` on `i32.gt_s` | signed maximum | tactic, tactic+smt (`bv_decide` closes both conditions by preprocessing; audited standard axioms), tactic+script |
| [SumTo](../../Silmaril/WasmSpec/SumTo/manifest.toml) | 1.0.0 | count-down loop | `n(n+1)/2` (mod 2^32) | tactic, tactic+script, all-in |
| [IsSorted](../../Silmaril/WasmSpec/IsSorted/manifest.toml) | 1.0.0 | loop over adjacent pairs of an `i32` array in memory | `1` iff the segment is sorted (signed), store unchanged; every-run total correctness | tactic (+ interpreter tests) |
| [InsertionSort](../../Silmaril/WasmSpec/InsertionSort/manifest.toml) | 1.0.0 | in-place insertion sort | sorted (signed) permutation, rest of the store unchanged; every-run total | tactic (+ interpreter tests) |
| [MergeSort](../../Silmaril/WasmSpec/MergeSort/manifest.toml) | 1.0.0 | recursive merge sort with a scratch buffer | sorted permutation, store unchanged outside array and buffer; every-run total | tactic (+ interpreter tests) |
| [BTree](../../Silmaril/WasmSpec/BTree/manifest.toml) | 1.0.1 (**partial**, superseded by 2) | the B-tree library of Watt et al. (ECOOP 2019): `oba_get`, `oba_find`, `btree_search` | OBA get/find proved (every-run total); search stated and tested, not provable as stated; insert/create stated | tactic (OBA) |
| [BTree v2](../../Silmaril/WasmSpec/BTree/V2/manifest.toml) | 2.0.0 | the B-tree library with `btree_insert` (node splitting, root growth, free-page list, `memory.grow`) and `btree_create` | OBA get/find and search (store unchanged); insert/create with an out-of-memory outcome and a memory frame; every-run total | tactic (+ interpreter tests) |

The generated `Rv64*` entries pose the Wasm side of RV64 functions reduced through the RV64
simulators ([wasm-sim-abi.md](wasm-sim-abi.md)). Their status is `stated` (a specification without
a solution yet), except `Rv64Absdiff`, which is verified.

## Layout of an entry

| Path | Contents |
| --- | --- |
| `Silmaril/WasmSpec/<Name>/manifest.toml` | name, version, status, program, specification, results, solutions |
| `Silmaril/WasmSpec/<Name>/<name>.wat` | the program (annotated WAT) |
| `Silmaril/WasmSpec/<Name>/Defs.lean` | **header**: the quoted program and the specification (`Spec`, often `CallSpec`) |
| `Silmaril/WasmSpec/<Name>/Thms.lean` | **header**: canonical results and their `#print axioms` audits (`#guard_msgs`) |
| `Silmaril/Proofs/WasmSpec/<Name>/<Mode>.lean` | one solution per module: `Tactic`, `Smt`, `Script`, `AllIn` |
| `Silmaril/WasmSpec/<Name>/V<n>/` | a later major version, namespace `Silmaril.WasmSpec.<Name>.V<n>` |

Clients import the two headers, never the proof modules. `Silmaril/WasmSpec/Common` is a shared
facility, not an entry: the call specifications (`Computes`, `CallSpec`) and the bridge from the
weakest-precondition calculus (`Silmaril.Wasm.Logic.Core`) to them.

## Solving modes and trust

| Mode | How | Trusted |
| --- | --- | --- |
| `tactic` | Lean tactics over the verification conditions of `Silmaril.Wasm.Logic` | Lean's kernel |
| `tactic+smt` | the same, with `bv_decide` | Lean's kernel only when the audit shows the standard axioms; solutions that add a native-evaluation axiom are not in this repository (`policy.toml`) |
| `tactic+script` | an external generator reads the annotated WAT and writes the Lean proof module | Lean's kernel (the generator is untrusted) |
| `all-in` | a generator plus model proposals for residual goals, each checked by Lean | Lean's kernel (generator and models are untrusted) |

Every solution lists its audited axioms in the manifest. `scripts/check-wasm-spec.py` rejects any
axiom other than `propext`, `Classical.choice` and `Quot.sound`, and requires the entry's
`Thms.lean` to audit each solution with `#print axioms`. The audits themselves are `#guard_msgs`
checks, so the Lean build fails when a proof's axioms change.

## Checking

`tools/wasm-spec-fuzz` runs the array programs (`IsSorted`, `InsertionSort`, `MergeSort`) and the
B-tree library (`BTree` v1 and v2) on the `wasmi` interpreter with random inputs, checks the
specified results, and checks that each `.wasm` file it runs is the byte list the Lean tests use
(`cargo test --release` in `tools/wasm-spec-fuzz`). These are tests, not proofs.

```sh
python3 -I scripts/check-wasm-spec.py
lake build --wfail Silmaril.WasmSpec.BTree.V2.Thms Silmaril.WasmSpec.IsSorted.Thms   # any entry's Thms
```

The `tactic+script` modules are generated by `tools/wasm-vc gen Silmaril/WasmSpec/<Name>`
([wasm-solvers.md](wasm-solvers.md)), which regenerates the committed `Script.lean` of Adder, Max
and SumTo byte for byte (it needs `lake` and `z3`). The `all-in` modules come from `wasm-vc agent`
with an external model command. Both tools are untrusted: their outputs are ordinary Lean
modules, checked like any other.

# Fold a same-source word subtraction to zero

Simple chapter 8's `SubNode.compute` returns a zero type when inputs 1
and 2 name the same node. `Node.peepholeOpt` materializes the constant
before calling `idealize`. This rule applies when the shared input
depends on the program arguments.
[SubNode.compute, lines 15–25](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L15-L25) ·
[Node.peepholeOpt, lines 243–254](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L254)

`SubSelf.step?` uses the existing typed word-producer enumeration.
`fold?` recovers the selected subtraction's actual ordered wires from
the SubZero checker and compares their addresses within the same typed
prefix. On acceptance it installs the existing word literal zero at
that binding's result slot. `fold_exact_source` proves exact typed wire
identity. `fold_sigs` and `fold_locals_eq` preserve the layout and every
producer value. `fold_eval_eq` and `step_eval_eq` preserve the native
return for every typed input in the existing `BitVec 64` model.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SubSelf/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SubSelf/Thms.lean)

The fixture replaces the subtraction of a shared, input-dependent
addition and retains a subtraction of distinct arguments. A downstream
subtraction reads the replacement through the original address and
wraps `0 - 1` to the maximum unsigned word. One call applies one fold.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/SubSelf/Regression.lean)

## Chapter 8 rule coverage

| Source rule | Checked native scope |
| --- | --- |
| [Right identities for addition](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L36-L39), [subtraction](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L37-L40), and [multiplication](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/MulNode.java#L33-L40) | The [right-identity pass](sea-of-nodes-pure-right-identity-pass.md) covers explicit right literals. The [shared scan](sea-of-nodes-pure-mul-order.md) commutes a literal-left multiplication. |
| [Same-input addition and add-spine changes](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L41-L88) | [Doubling](sea-of-nodes-pure-doubling.md) inserts literal two after the literal-fold check. [Add-chain folding](sea-of-nodes-pure-add-constant-chain.md) combines two nonzero right literals. The [right-spine step](sea-of-nodes-pure-right-spine.md) covers two distinct nonliteral adds. The [left-spine step](sea-of-nodes-pure-left-spine.md) checks the later comparator using supplied source IDs for nonliterals. The earlier non-add-left swap, off-spine comparator call, and recursive inner reevaluation remain open. |
| [Negated subtraction](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L37-L49) and [division by one](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/DivNode.java#L16-L34) | The word profile has no unary minus or division opcode. A division profile needs the source's signed rounding, overflow, and zero-divisor behavior. |
| [Same-input comparison](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L37-L48) and [operations across Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L93-L127) | Same-input comparison needs the native predicate profile. The Phi rule needs exact Region occurrence alignment for its rewritten operands and lies outside straight-line folding. |

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.SubSelf.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.SubSelf.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Regression
```

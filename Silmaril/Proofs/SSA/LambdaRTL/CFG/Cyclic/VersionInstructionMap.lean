module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning

universe u w

variable {V K : Type w} {F G : Type u} (f : F → G)

private theorem parseTerm_map (r : Region V K F) :
    Term.ofRegion? (r.mapOp f) = (Term.ofRegion? r).map (Term.mapOp f) := by
  induction r <;> simp_all [Term.ofRegion?, Region.mapOp, Term.mapOp, Option.map_bind,
    Option.bind_map, Function.comp_def]

private theorem parseBody_map (r : Region V K F) :
    Body.ofRegion? (r.mapOp f) = (Body.ofRegion? r).map (Body.mapOp f) := by
  induction r with
  | let1 _ _ _ ih | let2 _ _ _ _ ih =>
    simp only [Region.mapOp, Body.ofRegion?, ih, Option.map_map, Function.comp_def, Body.mapOp]
  | br => rfl
  | join => rfl
  | case op x l y r _ _ =>
    change (Term.ofRegion? ((Region.case op x l y r).mapOp f)).map Body.term = _
    rw [parseTerm_map]
    simp only [Body.ofRegion?, Option.map_map, Function.comp_def, Body.mapOp]

private theorem unwrap_map {o : Option (Body V K F)} {p : Option (Body V K G)}
    (h : p = o.map (Body.mapOp f)) (ho : o.isSome) (hp : p.isSome) :
    p.get hp = (o.get ho).mapOp f := by
  subst p
  exact Option.get_map

variable [DecidableEq V] [DecidableEq K]

private theorem versionBody_map (b : Body V K F) (dst : K → Option (List V))
    (regs : List V) (cur : V → Nat) (d : Nat) :
    versionBody (b.mapOp f) dst regs cur d = (versionBody b dst regs cur d).mapOp f := by
  unfold versionBody
  apply unwrap_map
  rw [Body.toRegion_mapOp, Version.version_mapOp, parseBody_map]

omit [DecidableEq V] [DecidableEq K] in
private theorem unpack_map (regs : List V) (src : V × Nat) (d : Nat)
    (r : Region (V × Nat) K F) :
    (Version.unpack regs src d r).mapOp f = Version.unpack regs src d (r.mapOp f) := by
  induction regs generalizing src d <;> simp_all [Version.unpack, Region.mapOp, Op.mapOp]

omit [DecidableEq V] [DecidableEq K] in
private theorem unpackBody_map (regs : List V) (src : V × Nat) (d : Nat)
    (b : Body (V × Nat) K F) :
    unpackBody regs src d (b.mapOp f) = (unpackBody regs src d b).mapOp f := by
  unfold unpackBody
  apply unwrap_map
  rw [Body.toRegion_mapOp, ← unpack_map, parseBody_map]

omit [DecidableEq K] in
private theorem registers_map (g : CFG V K F) : registers (g.mapOp f) = registers g := by
  simp [registers, CFG.mapOp, List.flatMap_map, Block.mapOp, Body.toRegion_mapOp,
    Version.fvList_mapOp]

omit [DecidableEq K] in
private theorem slots_map (g : CFG V K F) (b : Block V K F) :
    slots (g.mapOp f) (b.mapOp f) = slots g b := by
  rw [slots, slots, registers_map]
  rfl

omit [DecidableEq V] in
private theorem lookup_map (bs : List (K × Block V K F)) (k : K) :
    (bs.map (fun x => (x.1, x.2.mapOp f))).lookup k =
      (bs.lookup k).map (Block.mapOp f) := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.lookup]
    cases k == x.1 <;> simp only [ih, Option.map_some]

private theorem destinations_map (g : CFG V K F) :
    destinations (g.mapOp f) = destinations g := by
  funext k
  simp only [destinations, destinationsWith, CFG.mapOp, lookup_map, Option.map_map]
  cases g.blocks.lookup k with
  | none => rfl
  | some b => exact congrArg some (slots_map f g b)

private theorem compileBlock_map (g : CFG V K F) (b : Block V K F) :
    compileBlock (g.mapOp f) (b.mapOp f) = (compileBlock g b).mapOp f := by
  unfold compileBlock compileBlockWith
  rw [slots_map, destinations_map, registers_map]
  change Block.mk (b.param, 0) (.let2 _ _ _
    (unpackBody _ _ _ (versionBody (b.body.mapOp f) _ _ _ _))) = _
  rw [versionBody_map, unpackBody_map]
  rfl

theorem compile_mapOp (g : CFG V K F) : compile (g.mapOp f) = (compile g).mapOp f := by
  unfold compile
  rw [destinations_map, registers_map]
  change CFG.mk (versionBody (g.entry.mapOp f) _ _ _ _) _ = _
  rw [versionBody_map]
  simp only [CFG.mapOp, List.map_map, Function.comp_def]
  change CFG.mk _ (g.blocks.map (fun x => (x.1, compileBlock (g.mapOp f) (x.2.mapOp f)))) = _
  simp only [compileBlock_map]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion

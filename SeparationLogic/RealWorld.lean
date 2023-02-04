import SeparationLogic.Basic
import Mathlib
#check 42

#print Equiv
#check IO.RealWorld

opaque ST.RealWorldPointed : NonemptyType.{0}

abbrev ST.RealWorld := ST.RealWorldPointed.type

instance : Nonempty (ST.RealWorld) :=
  Nonempty.intro (Classical.choice ST.RealWorldPointed.property)

/-

remainder lean dynamic allocation allocation axioms

@[extern "lean_st_mk_ref"]
opaque mkRef {σ α} (a : α) : ST σ (Ref σ α) := pure { ref := Classical.choice RefPointed.property, h := Nonempty.intro a }
@[extern "lean_st_ref_get"]
opaque Ref.get {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_set"]
opaque Ref.set {σ α} (r : @& Ref σ α) (a : α) : ST σ Unit
@[extern "lean_st_ref_swap"]
opaque Ref.swap {σ α} (r : @& Ref σ α) (a : α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_take"]
unsafe opaque Ref.take {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_ptr_eq"]
opaque Ref.ptrEq {σ α} (r1 r2 : @& Ref σ α) : ST σ Bool

-/

#print Equiv
def Heap.new_pointer (m:Heap) : Heap.Pointer := Finset.next_elem m.domain

axiom Heap.RealWorldEquiv : Equiv Heap ST.RealWorld
axiom Heap.RefEquiv {α} : Equiv Pointer (ST.Ref ST.RealWorld α)

@[simp] noncomputable instance : Coe Heap.Pointer (ST.Ref ST.RealWorld α) := ⟨Heap.RefEquiv.toFun⟩
@[simp] noncomputable instance : Coe (ST.Ref ST.RealWorld α) Heap.Pointer := ⟨Heap.RefEquiv.invFun⟩

@[simp] noncomputable instance : Coe Heap ST.RealWorld := ⟨Heap.RealWorldEquiv.toFun⟩
@[simp] noncomputable instance : Coe ST.RealWorld Heap := ⟨Heap.RealWorldEquiv.invFun⟩

def ST.evalST {σ α} (st:ST σ α) (m:σ) : α × σ :=
  match st m with
  | EStateM.Result.ok x m' => (x, m')
  | EStateM.Result.error ex _ => nomatch ex

open Heap in
axiom ST.mkRefAxiom {α} (x:α) (m:RealWorld) :
  let (ref, m') : Ref RealWorld α × RealWorld := evalST (Prim.mkRef x) m
  m' = (RealWorldEquiv.invFun m) ∪ {(RefEquiv.invFun ref, ⟨α, x⟩)} ∧
  ref = new_pointer m

open Heap in
axiom ST.getAxiom {α} (ref:Ref RealWorld α) (m:RealWorld) :
  let (x, m') : α × RealWorld := evalST (Prim.Ref.get ref) m
  m = m' ∧ ∀ h:(RefEquiv.invFun ref) ∈ (RealWorldEquiv.invFun m).domain,
    (RealWorldEquiv.invFun m).val ⟨ref, h⟩ = ⟨α, x⟩

open Heap in
axiom ST.setAxiom {α} (ref:Ref RealWorld α) (x:α) (m:RealWorld) :
  let (_, m') := evalST (Prim.Ref.set ref x) m
  RefEquiv.invFun ref ∈ (RealWorldEquiv.invFun m).domain ∧
  m' = {(RefEquiv.invFun ref, ⟨α, x⟩)} ∪ (RealWorldEquiv.invFun m)

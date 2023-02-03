import Mathlib
import Lean
import Mathlib.Data.Finset.Basic

universe u v w

def Finset.next_elem (s:Finset Nat) : Nat :=
  match Finset.max s with
  | some x => Nat.succ x
  | none => 0

theorem Finset.next_elem_not_in_self (s:Finset Nat) : next_elem s ∉ s :=
by
  intro h1
  simp only [next_elem] at h1
  generalize h2 : Finset.max s = x
  rw [h2] at h1
  cases x with
  | none =>
    have := Finset.max_eq_bot.1 h2
    simp only [this, not_mem_empty] at *
  | some x =>
    simp only at *
    have := Finset.le_max h1
    rw [h2] at this
    simp only [LE.le, Option.mem_def, Option.some.injEq, Nat.lt_eq, exists_eq_left'] at this
    have := this (.succ x) (by trivial)
    simp_arith at this

structure Heap.Cell where
  type: Type 0
  val: type


structure Heap where
  domain : Finset Nat
  val : {x // x ∈ domain} → Heap.Cell

instance : Inhabited Heap where
  default := ⟨∅, fun x => by
    apply False.elim
    cases x.property
  ⟩

instance : EmptyCollection Heap where
  emptyCollection := default

def Heap.eval (m:Heap) (x:Nat) : Option Cell :=
  dite (x ∈ m.domain) (fun h => some <| m.val ⟨x, h⟩) (fun _ => none)

theorem Heap.eval_eq_thm : ∀ m₁ m₂ : Heap,
  (∀ x, eval m₁ x = eval m₂ x) → m₁ = m₂ :=
by
  intro ⟨d1, v1⟩ ⟨d2, v2⟩ h1
  have : ∀ x, x ∈ d1 ↔ x ∈ d2 := by
    intro x
    constructor <;> intro h2
    <;> apply by_contradiction
    <;> intro h3
    <;> have := h1 x
    <;> simp only [eval, h2, h3, dite_true, dite_false] at this

  have : d1 = d2 := Finset.ext_iff.2 this
  induction this
  simp only [mk.injEq, heq_eq_eq, true_and]

  apply funext
  intro x
  have := h1 x
  simp only [eval, Finset.coe_mem, Subtype.coe_eta, dite_eq_ite, ite_true, Option.some.injEq] at this
  assumption

#check Disjoint
#check Finset.disjUnion
def Heap.disjoint (m₁ m₂: Heap) : Prop := Disjoint m₁.domain m₂.domain

theorem Heap.disjoint_thm (m₁ m₂: Heap) : disjoint m₁ m₂ = (m₁.domain ∩ m₂.domain = ∅) := by
  simp only [disjoint, Finset.disjoint_iff_ne, ne_eq, eq_iff_iff]
  constructor
  . intros h1
    rw [Finset.ext_iff]
    simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and]
    intro a h2 h3
    apply h1 a h2 a h3 rfl
  . intros h1 a h2 b h3 h4
    simp only [Finset.ext_iff, Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and] at h1
    induction h4
    apply h1 a
    <;> assumption



infixl:62 " /// " => Heap.disjoint

instance : Union Heap := ⟨fun m₁ m₂ => ⟨
  m₁.domain ∪ m₂.domain,
  fun x => dite (x.1 ∈ m₁.domain) (fun h => m₁.val ⟨x.val, h⟩)
  (fun h1 => dite (x.1 ∈ m₂.domain) (fun h => m₂.val ⟨x.val, h⟩) (by
    intro h2
    apply False.elim
    have := x.property
    simp only [Finset.mem_union] at this
    apply Or.elim this
    <;> intro h
    . exact h1 h
    . exact h2 h
  ))
⟩⟩

@[simp] instance : Membership Nat Heap := ⟨fun x m => x ∈ m.domain⟩

instance {x:Nat} {m:Heap} : Decidable (x ∈ m) := inferInstanceAs (Decidable (x ∈ m.domain))

@[simp] def Heap.join := @Union.union Heap _

@[simp] theorem Heap.eval_join_thm : ∀ m₁ m₂ x,
  eval (m₁ ∪ m₂) x = match eval m₁ x with
    | none => eval m₂ x
    | some x => some x
:= by
  intro m₁ m₂ x
  apply @Classical.byCases (x ∈ m₁.domain) <;>
  apply @Classical.byCases (x ∈ m₂.domain) <;>
  intro h1 h2 <;> simp only [
    eval, h1, h2, Union.union, Finset.mem_mk,
    Multiset.mem_ndunion, Finset.mem_val,
    or_self, or_true, or_false, dite_true, dite_false]

#print Associative

theorem Heap.join_is_Associative : ∀ m₁ m₂ m₃:Heap, m₁ ∪ (m₂ ∪ m₃) = (m₁ ∪ m₂) ∪ m₃ := by
  intro m1 m2 m3
  apply Heap.eval_eq_thm
  intro x
  simp
  cases eval m1 x <;>
  cases eval m2 x <;>
  simp only

instance : Associative Heap.join := by
  simp only [Associative]
  intros
  apply Eq.symm
  apply Heap.join_is_Associative

@[symm] theorem Heap.disjoint_is_symmetric : ∀ m₁ m₂, m₁ /// m₂ → m₂ /// m₁ :=
by
  simp only [Symmetric, disjoint_thm]
  intro m₁ m₂ h
  have h := Finset.ext_iff.1 h
  apply Finset.ext_iff.2
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and] at *
  intro x h1 h2
  apply h x h2 h1

theorem Heap.disjoint_symm : ∀ m₁ m₂, m₁ /// m₂ ↔ m₂ /// m₁ :=
by
  intros
  constructor
  <;> apply Heap.disjoint_is_symmetric

theorem Heap.join_symm : ∀ m₁ m₂, m₁ /// m₂ → m₁ ∪ m₂ = m₂ ∪ m₁ :=
by
  intro m₁ m₂ h1
  apply eval_eq_thm
  intro x
  simp only [eval_join_thm]
  apply @Classical.byCases (x ∈ m₁.domain) <;>
  apply @Classical.byCases (x ∈ m₂.domain) <;>
  intro h2 h3 <;> simp [eval, h2, h3]
  apply False.elim
  simp only [disjoint_thm] at h1
  have := Finset.ext_iff.1 h1 x
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and] at this
  apply this
  <;> assumption

@[simp] theorem Heap.eval_empty :
  ∀ x, eval ∅ x = none :=
by
  intro x
  simp only [eval, EmptyCollection.emptyCollection]
  simp only [default, dite_false, Finset.not_mem_empty]

@[simp] theorem Heap.disjoint_empty_left :
  ∀ m:Heap, disjoint m ∅ :=
by
  simp only [disjoint, EmptyCollection.emptyCollection]
  simp only [default, Finset.disjoint_empty_right, forall_const]

@[simp] theorem Heap.disjoint_empty_right :
  ∀ m:Heap, disjoint ∅ m :=
by
  simp only [disjoint, EmptyCollection.emptyCollection]
  simp only [default, Finset.disjoint_empty_left, forall_const]

@[simp] theorem Heap.join_empty_right :
  ∀ m:Heap, ∅ ∪ m = m :=
by
  intro m
  apply eval_eq_thm
  intro x
  simp only [eval_join_thm, eval_empty]

@[simp] theorem Heap.join_empty_left :
  ∀ m:Heap, m ∪ ∅ = m :=
by
  intro m
  apply eval_eq_thm
  intro x
  simp only [eval_empty, eval_join_thm]
  cases eval m x
  <;> simp only


@[simp] theorem Heap.join_domain :
  ∀ m₁ m₂ : Heap, (m₁ ∪ m₂).domain = m₁.domain ∪ m₂.domain :=
by
  intro m₁ m₂
  simp [Union.union]

@[simp] theorem Heap.disjoint_joint_comp1 :
  ∀ m₁ m₂ m₃, m₁ /// m₂ ∪ m₃ ↔ (m₁ /// m₂ ∧ m₁ /// m₃) :=
by
  intro m₁ m₂ m₃
  constructor
  <;> intro h
  <;> simp only [disjoint_thm, join_domain] at *
  . have h1 := Finset.ext_iff.1 h
    constructor <;> apply Finset.ext_iff.2
    <;> simp only [Finset.mem_union, Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and] at *
    . intro x h2 h3
      apply h1 x
      assumption
      apply Or.inl
      assumption
    . intro x h2 h3
      apply h1 x
      assumption
      apply Or.inr
      assumption
  . apply Finset.ext_iff.2
    have h1 := Finset.ext_iff.1 h.1
    have h2 := Finset.ext_iff.1 h.2
    simp only [Finset.mem_inter, Finset.mem_union, Finset.not_mem_empty, iff_false, not_and] at *
    intro x h3 h4
    cases h4
    . apply h1 x <;> assumption
    . apply h2 x <;> assumption

@[simp] theorem Heap.disjoint_joint_comp2 :
  ∀ m₁ m₂ m₃, m₁ ∪ m₂ /// m₃ ↔ (m₁ /// m₃ ∧ m₂ /// m₃) :=
by
  intro m₁ m₂ m₃
  simp [disjoint_symm]


instance : Symmetric Heap.disjoint := Heap.disjoint_is_symmetric

def Heap.context_stability (p:Heap → Prop) := ∀ m₁ m₂, m₁ /// m₂ → p m₁ → p (m₁ ∪ m₂)

def Heap.prop := { p:Heap → Prop // context_stability p }

@[simp] def Heap.pure_prop_definition (p:Prop) : Heap → Prop := fun _ => p

def Heap.pure_prop_stability (p:Prop) : context_stability (pure_prop_definition p) :=
  by simp [context_stability, pure_prop_definition]

@[simp] def Heap.pure_prop (p:Prop) : Heap.prop :=
  ⟨pure_prop_definition p, pure_prop_stability p⟩

@[simp] def Heap.assign_prop_definition (ref:Nat) (cell:Cell) : Heap → Prop :=
  fun m => eval m ref = some cell

def Heap.assign_prop_stability (ref:Nat) (cell:Cell) : context_stability (assign_prop_definition ref cell) :=
by
  simp only [context_stability, assign_prop_definition, eval_join_thm]
  intro m₁ m₂ _ h2
  generalize h3 : eval m₁ ref = x₁
  generalize h4 : eval m₂ ref = x₂
  cases x₁ <;> cases x₂ <;> simp
  case none.none =>
    rw [h3] at h2
    cases h2
  case none.some x =>
    rw [h3] at h2
    cases h2
  case some.none x =>
    rw [h3] at h2
    cases h2
    rfl
  case some.some x y =>
    rw [h3] at h2
    cases h2
    rfl

@[simp] def Heap.assign_prop (ref:Nat) (cell:Cell) : Heap.prop :=
  ⟨
    assign_prop_definition ref cell,
    assign_prop_stability ref cell
  ⟩

@[simp] def Heap.star_prop_definition (P Q:Heap.prop) : Heap → Prop :=
  fun m => ∃ m₁ m₂,
    m = m₁ ∪ m₂ ∧ m₁ /// m₂ ∧ P.val m₁ ∧ Q.val m₂


def Heap.star_prop_stability (P Q:Heap.prop) : context_stability (star_prop_definition P Q) :=
by
  intro m m' h1 h2
  apply Exists.elim h2
  intro m₁ h2
  apply Exists.elim h2
  intro m₂ h2
  -- use m₁ and m₂ ∪ m'
  apply Exists.intro m₁
  apply Exists.intro (m₂ ∪ m')
  constructor
  . simp only [h2.1]
    have := Heap.join_is_Associative
    simp only [Associative] at this
    rw [this]
  . constructor
    . simp only [disjoint_joint_comp1]
      simp only [h2.1, disjoint_joint_comp2] at h1
      constructor
      . apply h2.2.1
      . exact h1.1
    . constructor
      . exact h2.2.2.1
      . apply Q.property
        . simp only [h2.1, disjoint_joint_comp2] at h1
          exact h1.2
        . exact h2.2.2.2

@[simp] def Heap.star_prop (P Q:Heap.prop) : Heap.prop :=
  ⟨star_prop_definition P Q, star_prop_stability P Q⟩

@[simp] def Heap.magic_prop_definitoin (P Q:Heap.prop) : Heap → Prop :=
  fun m : Heap =>
    ∀ m':Heap, m /// m' → P.val m' → Q.val (m ∪ m')

def Heap.magic_prop_stability (P Q:Heap.prop) : context_stability (magic_prop_definitoin P Q) :=
by
  intro m₁ m₂ h1 h2 m' h3 h4
  have h2 := h2 (m₂ ∪ m')
  rw [join_is_Associative] at h2
  apply h2
  simp only [disjoint_joint_comp1, disjoint_joint_comp2] at *
  constructor
  . apply h1
  . apply h3.1
  . rw [join_symm] <;>
    simp only [disjoint_joint_comp2] at h3
    apply P.property
    rw [disjoint_symm]
    exact h3.2
    assumption
    exact h3.2


@[simp] def Heap.magic_prop (P Q:Heap.prop) : Heap.prop :=
  ⟨Heap.magic_prop_definitoin P Q, Heap.magic_prop_stability P Q⟩

@[simp] def Heap.exists_prop_definition {α:Sort u} (prop:α → Heap.prop) : Heap → Prop :=
  λ m: Heap => ∃ x:α, (prop x).val m

def Heap.exists_prop_stability {α: Sort u} (prop: α → Heap.prop) :
  context_stability (@exists_prop_definition α prop) :=
by
  simp only [context_stability, exists_prop_definition, forall_exists_index]
  intro m₁ m₂ h1 x h2
  apply Exists.intro x
  apply (prop x).property
  <;> assumption

@[simp] def Heap.exists_prop {α:Sort u} (prop:α → Heap.prop) : Heap.prop :=
  ⟨exists_prop_definition prop, exists_prop_stability prop⟩

@[simp] def Heap.forall_prop_definition {α:Sort u} (prop:α → Heap.prop) : Heap → Prop :=
  λ m:Heap => ∀ x:α, (prop x).val m

def Heap.forall_prop_stability {α:Sort u} (prop:α → Heap.prop) : context_stability (forall_prop_definition prop) :=
by
  simp only [context_stability]
  intro m₁ m₂ h1 h2 x
  apply (prop x).property
  assumption
  apply h2

@[simp] def Heap.forall_prop {α:Sort u} (prop:α → Heap.prop) : Heap.prop :=
  ⟨forall_prop_definition prop, forall_prop_stability prop⟩

@[simp] def Heap.and_prop_definition (P Q:Heap.prop) : Heap → Prop :=
  λ m:Heap => P.val m ∧ Q.val m

def Heap.and_prop_stability (P Q:Heap.prop) : context_stability (and_prop_definition P Q) :=
by
  simp only [context_stability, and_prop_definition, and_imp]
  intro m₁ m₂ h1 h2 h3
  constructor
  . apply P.property
    <;> assumption
  . apply Q.property
    <;> assumption

@[simp] def Heap.and_prop (P Q:Heap.prop) : Heap.prop :=
  ⟨and_prop_definition P Q, and_prop_stability P Q⟩

@[simp] def Heap.or_prop_definition (P Q:Heap.prop) : Heap → Prop :=
  λ m:Heap => P.val m ∨ Q.val m

def Heap.or_prop_stability (P Q:Heap.prop) : context_stability (or_prop_definition P Q) :=
by
  simp only [context_stability]
  intro m₁ m₂ h1 h2
  cases h2
  . apply Or.inl
    apply P.property
    <;> assumption
  . apply Or.inr
    apply Q.property
    <;> assumption


@[simp] def Heap.or_prop (P Q:Heap.prop) : Heap.prop :=
  ⟨or_prop_definition P Q, or_prop_stability P Q⟩

syntax " ⌜ " term " ⌝ " : term -- type as `ulcorner` and `urcorner`
syntax " ⌜ " " ⌝ " : term
macro_rules
| `(⌜ $p:term ⌝) => `( Heap.pure_prop $p )
| `( ⌜⌝ ) => `( Heap.pure_prop True )

syntax term " ↦ " term : term -- type as `mapsto`
macro_rules
| `( $x:term ↦ $y:term ) => `( Heap.assign_prop $x $y )

infixr:67 " ⋆ " => Heap.star_prop -- type as `star`

infixr:65 " -⋆ " => Heap.magic_prop

infixr:35 " ∧ᴴ " => Heap.and_prop

infixr:30 " ∨ᴴ " => Heap.or_prop

#print Exists


open Lean in
open TSyntax.Compat in
macro "∃ᴴ " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Heap.exists_prop xs b

open Lean in
open TSyntax.Compat in
macro "∀ᴴ " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Heap.forall_prop xs b

#check (∃ᴴ x, ⌜ x ⌝) ⋆ ∀ᴴ y, ⌜ y ⌝


inductive Tree where
| Leaf : Tree
| Node : Tree → Nat → Tree → Tree

structure Tree_record where
  l : Option Nat -- mutable sub-tree
  x : Nat -- item
  r : Option Nat -- mutable sub-tree

def is_tree (x:Option Nat) : Tree → Heap.prop
| .Leaf => ⌜x=none⌝
| .Node l y r => ∃ᴴ (x':Nat) (xl xr:Option Nat),
  ⌜x=some x'⌝ ⋆ is_tree xl l ⋆ is_tree xr r ⋆ x' ↦ ⟨Tree_record, ⟨xl, y, xr⟩⟩

#print is_tree


@[simp] theorem Heap.star_magic_reduction (P Q:Heap.prop) : ∀ m, (P ⋆ (P -⋆ Q)).val m → Q.val m :=
by
  intro m1
  simp only [star_prop, star_prop_definition, magic_prop, magic_prop_definitoin, forall_exists_index, and_imp]
  intro m2 m3 h1 h2 h3 h4
  have := h4 m2
  simp at *
  rw [join_symm, disjoint_symm, <-h1] at this
  apply this
  <;> assumption
  rw [disjoint_symm]
  assumption


@[symm] theorem Heap.star_is_symmetric (P Q:Heap.prop) : ∀ m, (P ⋆ Q).val m → (Q ⋆ P).val m :=
by
  intro m
  simp only [star_prop, star_prop_definition]
  intro h1
  apply Exists.elim h1
  intro m1 h1
  apply Exists.elim h1
  intro m2 h1
  rw [join_symm, disjoint_symm] at h1
  apply Exists.intro m2
  apply Exists.intro m1
  constructor
  . apply h1.1
  . constructor
    . apply h1.2.1
    . constructor
      . apply h1.2.2.2
      . apply h1.2.2.1
  apply h1.2.1


theorem Heap.star_symm (P Q:Heap.prop) : ∀ m, (P ⋆ Q).val m ↔ (Q ⋆ P).val m :=
by
  intro
  constructor
  <;> apply Heap.star_is_symmetric


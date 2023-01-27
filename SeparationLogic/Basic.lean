import Mathlib

import Mathlib.Data.Finset.Basic

universe u v w


def Finset.next_elem (s:Finset Nat) : Nat :=
  match Finset.max s with
  | some x => Nat.succ x
  | none => 0

theorem Finset.next_elem_not_in_self (s:Finset Nat) : next_elem s ∉ s :=
by
  intro h1
  simp [next_elem] at h1
  generalize h2 : Finset.max s = x
  rw [h2] at h1
  cases x with
  | none =>
    have := Finset.max_eq_bot.1 h2
    simp [this] at *
  | some x =>
    simp at *
    have := Finset.le_max h1
    rw [h2] at this
    simp [LE.le] at this
    have := this (.succ x) (by trivial)
    simp_arith at this

structure Heap.Cell where
  type: Type 0
  val: type


structure Heap where
  domain : Finset Nat
  val : {x // x ∈ domain} → Heap.Cell

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
    <;> simp [eval, h2, h3] at this

  have : d1 = d2 := Finset.ext_iff.2 this
  induction this
  simp

  apply funext
  intro x
  have := h1 x
  simp [eval] at this
  assumption

def Heap.disjoint (m₁ m₂: Heap) : Prop := m₁.domain ∩ m₂.domain = ∅

infixl:62 " /// " => Heap.disjoint

instance : Union Heap := ⟨fun m₁ m₂ => ⟨
  m₁.domain ∪ m₂.domain,
  fun x => dite (x.1 ∈ m₁.domain) (fun h => m₁.val ⟨x.val, h⟩)
  (fun h1 => dite (x.1 ∈ m₂.domain) (fun h => m₂.val ⟨x.val, h⟩) (by
    intro h2
    apply False.elim
    have := x.property
    simp at this
    apply Or.elim this
    <;> intro h
    . exact h1 h
    . exact h2 h
  ))
⟩⟩

@[simp] instance : Membership Nat Heap := ⟨fun x m => x ∈ m.domain⟩

@[simp] def Heap.join := @Union.union Heap _

@[simp] theorem Heap.eval_join_thm : ∀ m₁ m₂ x,
  eval (m₁ ∪ m₂) x = match eval m₁ x with
    | none => eval m₂ x
    | some x => some x
:= by
  intro m₁ m₂ x
  apply @Classical.byCases (x ∈ m₁.domain) <;>
  apply @Classical.byCases (x ∈ m₂.domain) <;>
  intro h1 h2 <;> simp [eval, h1, h2, Union.union]

theorem Heap.join_is_Associative : Associative Heap.join := by
  intro m1 m2 m3
  apply Heap.eval_eq_thm
  intro x
  simp
  cases eval m1 x <;>
  cases eval m2 x <;>
  simp

instance : Associative Heap.join := Heap.join_is_Associative

@[symm] theorem Heap.disjoin_is_symmetric : ∀ m₁ m₂, m₁ /// m₂ → m₂ /// m₁ :=
by
  simp [Symmetric, disjoint]
  intro m₁ m₂ h
  have h := Finset.ext_iff.1 h
  apply Finset.ext_iff.2
  simp at *
  intro x h1 h2
  apply h x h2 h1

instance : Symmetric Heap.disjoint := Heap.disjoin_is_symmetric

def Heap.Prop := { p:Heap → Prop // ∀ m₁ m₂, m₁ /// m₂ → p m₁ → p (join m₁ m₂) }

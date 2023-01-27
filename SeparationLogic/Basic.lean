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

def Finset.not_in_union {α:Type u} {β:Sort v} [DecidableEq α] : ∀
  (m₁ m₂:Finset α) (x:α), x ∈ m₁ ∪ m₂ → x ∉ m₁ → x ∉ m₂ → β :=
by
  intro m1 m2 x h1 h2 h3
  apply False.elim
  simp at h1
  cases h1 with
  | inl h =>
    exact h2 h
  | inr h =>
    exact h3 h

def Heap.join (m₁ m₂ : Heap) : Heap := ⟨
  m₁.domain ∪ m₂.domain,
  fun x => dite (x.1 ∈ m₁.domain) (fun h => m₁.val ⟨x.val, h⟩)
  (fun h1 => dite (x.1 ∈ m₂.domain) (fun h => m₂.val ⟨x.val, h⟩) (fun h2 =>
    @Finset.not_in_union Nat _ _ m₁.domain m₂.domain x.val x.property h1 h2
  ))
⟩

@[simp] theorem Heap.eval_join_thm : ∀ m₁ m₂ : Heap, ∀ i,
  eval (join m₁ m₂) i =
    match eval m₁ i with
    | some x => some x
    | none => eval m₂ i
:= by
  intro ⟨d1, f1⟩ ⟨d2, f2⟩
  intro i
  apply @Classical.byCases (i ∈ d1)
  <;> apply @Classical.byCases (i ∈ d2)
  <;> intro h1 h2 <;> simp [eval, join, h1, h2]

theorem Heap.join_is_Associative : Associative Heap.join := by
  intro m1 m2 m3
  apply Heap.eval_eq_thm
  intro x
  simp
  cases eval m1 x <;>
  cases eval m2 x <;>
  simp

#check Finset.ext_iff

theorem Heap.disjoint_is_symmetric : Symmetric disjoint := by
  intro m1 m2
  simp [disjoint]
  have : m1.domain ∩ m2.domain = m2.domain ∩ m1.domain := by
    apply Finset.ext_iff.2; simp
    intro x; constructor
    <;> intro h
    <;> exact And.intro h.2 h.1

  rw [this]
  intros
  trivial

@[simp] theorem Heap.join_domain :
  ∀ m₁ m₂, (join m₁ m₂).domain = m₁.domain ∪ m₂.domain :=
by
  intro m1 m2
  simp [join]

theorem Heap.disjoint_of_joint :
  ∀ m₁ m₂ m₃, disjoint m₁ m₃ ∧ disjoint m₂ m₃ → disjoint (join m₁ m₂) m₃ :=
by
  intro ⟨d1, f1⟩ ⟨d2, f2⟩ ⟨d3, f3⟩
  simp [disjoint]
  intro h1 h2
  apply Finset.ext_iff.2
  have h1 := Finset.ext_iff.1 h1
  have h2 := Finset.ext_iff.1 h2
  intro x
  constructor <;> intro h
  . apply False.elim
    simp at h h1 h2
    cases h.1
    apply h1 x
    assumption
    exact h.2
    apply h2 x
    assumption
    exact h.2
  . apply False.elim
    cases h


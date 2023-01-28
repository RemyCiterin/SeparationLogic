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
  intro h1 h2 <;> simp [eval, h1, h2, Union.union]

#print Associative

theorem Heap.join_is_Associative : ∀ m₁ m₂ m₃:Heap, m₁ ∪ (m₂ ∪ m₃) = (m₁ ∪ m₂) ∪ m₃ := by
  intro m1 m2 m3
  apply Heap.eval_eq_thm
  intro x
  simp
  cases eval m1 x <;>
  cases eval m2 x <;>
  simp

instance : Associative Heap.join := by
  simp only [Associative]
  intros
  apply Eq.symm
  apply Heap.join_is_Associative

@[symm] theorem Heap.disjoint_is_symmetric : ∀ m₁ m₂, m₁ /// m₂ → m₂ /// m₁ :=
by
  simp [Symmetric, disjoint]
  intro m₁ m₂ h
  have h := Finset.ext_iff.1 h
  apply Finset.ext_iff.2
  simp at *
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
  simp
  apply @Classical.byCases (x ∈ m₁.domain) <;>
  apply @Classical.byCases (x ∈ m₂.domain) <;>
  intro h2 h3 <;> simp [eval, h2, h3]
  apply False.elim
  simp [disjoint] at h1
  have := Finset.ext_iff.1 h1 x
  simp at this
  apply this
  <;> assumption

@[simp] theorem Heap.eval_empty :
  ∀ x, eval ∅ x = none :=
by
  intro x
  simp [eval, EmptyCollection.emptyCollection]
  simp [default]

@[simp] theorem Heap.disjoint_empty_left :
  ∀ m:Heap, disjoint m ∅ :=
by
  simp [disjoint, EmptyCollection.emptyCollection]
  simp [default]

@[simp] theorem Heap.disjoint_empty_right :
  ∀ m:Heap, disjoint ∅ m :=
by
  simp [disjoint, EmptyCollection.emptyCollection]
  simp [default]

@[simp] theorem Heap.join_empty_right :
  ∀ m:Heap, ∅ ∪ m = m :=
by
  intro m
  apply eval_eq_thm
  intro x
  simp

@[simp] theorem Heap.join_empty_left :
  ∀ m:Heap, m ∪ ∅ = m :=
by
  intro m
  apply eval_eq_thm
  intro x
  simp
  cases eval m x
  <;> simp


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
  <;> simp [disjoint] at *
  . have h1 := Finset.ext_iff.1 h
    constructor <;> apply Finset.ext_iff.2
    <;> simp at *
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
    simp at *
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

def Heap.Prop := { p:Heap → Prop // ∀ m₁ m₂, m₁ /// m₂ → p m₁ → p (m₁ ∪ m₂) }

def Heap.PureProp (p:Prop) : Heap.Prop :=
  ⟨fun _ => p, by simp⟩

def Heap.AssignProp (ref:Nat) (cell:Cell) : Heap.Prop :=
  ⟨
    fun m => eval m ref = some cell,
    by
      simp
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
  ⟩

def Heap.StarProp (P Q:Heap.Prop) : Heap.Prop :=
⟨
  fun m => ∃ m₁ m₂,
    m = m₁ ∪ m₂ ∧ m₁ /// m₂ ∧ P.val m₁ ∧ Q.val m₂,
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
      . simp [h2.1]
        have := Heap.join_is_Associative
        simp [Associative] at this
        rw [this]
      . constructor
        . simp
          simp [h2.1] at h1
          constructor
          . apply h2.2.1
          . exact h1.1
        . constructor
          . exact h2.2.2.1
          . apply Q.property
            . simp [h2.1] at h1
              exact h1.2
            . exact h2.2.2.2
⟩

def Heap.MagicProp (P Q:Heap.Prop) : Heap.Prop :=
⟨
  fun m:Heap =>
    ∀ m':Heap, (m /// m') → P.val m' → Q.val (m ∪ m'),
  by
    intro m₁ m₂ h1 h2 m' h3 h4
    have h2 := h2 (m₂ ∪ m')
    rw [join_is_Associative] at h2
    apply h2
    simp at *
    constructor
    . apply h1
    . apply h3.1
    . rw [join_symm] <;>
      simp at h3
      apply P.property
      rw [disjoint_symm]
      exact h3.2
      assumption
      exact h3.2
⟩


syntax " ⌜ " term " ⌝ " : term -- type as `ulcorner` and `urcorner`
syntax " ⌜ " " ⌝ " : term
macro_rules
| `(⌜ $p:term ⌝) => `( Heap.PureProp $p )
| `( ⌜⌝ ) => `( Heap.PureProp True )

syntax term " ↦ " term : term -- type as `mapsto`
macro_rules
| `( $x:term ↦ $y:term ) => `( Heap.AssignProp $x $y )

infixr:67 " ⋆ " => Heap.StarProp -- type as `star`

infixr:65 " -⋆ " => Heap.MagicProp

@[simp] theorem Heap.star_magic_reduction (P Q:Heap.Prop) : ∀ m, (P ⋆ (P -⋆ Q)).val m → Q.val m :=
by
  intro m1
  simp [Heap.StarProp, Heap.MagicProp]
  intro m2 m3 h1 h2 h3 h4
  have := h4 m2
  simp at *
  rw [join_symm, disjoint_symm, <-h1] at this
  apply this
  <;> assumption
  rw [disjoint_symm]
  assumption

@[symm] theorem Heap.star_is_symmetric (P Q:Heap.Prop) : ∀ m, (P ⋆ Q).val m → (Q ⋆ P).val m :=
by
  intro m
  simp only [StarProp]
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

theorem Heap.star_symm (P Q:Heap.Prop) : ∀ m, (P ⋆ Q).val m ↔ (Q ⋆ P).val m :=
by
  intro
  constructor
  <;> apply Heap.star_is_symmetric


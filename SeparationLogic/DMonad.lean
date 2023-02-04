import SeparationLogic.Basic
import DijkstraMonad.Basic
import DijkstraMonad.Notations
import SeparationLogic.RealWorld
universe u v

def Heap.HeapM (α:Type u) := ST.RealWorld → α × ST.RealWorld
def Heap.HeapM.wp (α:Type u) :=
  {f:(α → Heap.prop) → Heap.prop // ∀ p1 p2, (∀ x, p1 x ⊧ p2 x) → f p1 ⊧ f p2 }

noncomputable def Heap.HeapMApplyEquiv (α:Type u) (t:HeapM α) : Heap → α × Heap :=
  fun m => let (x, m') := t m; (x, m')

#print Heap.HeapMApplyEquiv

instance : Monad Heap.HeapM where
  pure x := fun m => (x, m)
  bind f1 f2 := fun m => let (a, m') := f1 m; f2 a m'

instance : Monad Heap.HeapM.wp where
  pure x := ⟨fun p => p x, by
    intro p1 p2 h1 m h2
    simp only at *
    apply h1
    assumption
  ⟩
  bind f1 f2 := ⟨
    fun p => f1.val (fun x => (f2 x).1 p),
    by
      intro p1 p2 h1 m h2
      simp only at *
      apply f1.2 fun x => (f2 x).1 p1
      . intro x m h3
        apply (f2 x).2 p1
        assumption
        assumption
      . assumption
  ⟩

#check @pure (Heap.HeapM.wp)

open OrderedMonad
open EffectObservation

instance : OrderedMonad Heap.HeapM.wp where
  leW p1 p2 := ∀ p, p2.1 p ⊧ p1.1 p

  trans := by
    intro α a b c f1 f2 p m h1
    simp only [Heap.models] at *
    apply f1
    apply f2
    assumption

  refl := by
    intro α a p m h1
    assumption

  bindW := by
    intro α β w w' f f' f1 f2 p m h1
    simp only [bind] at *
    apply f1 fun x => (f x).1 p
    apply w'.2 fun x => (f' x).1 p
    . intro x m h1
      apply f2
      assumption
    . assumption

#check θ


instance : EffectObservation Heap.HeapM Heap.HeapM.wp where
  θ {α:Type u} (m:Heap.HeapM α) :=
    have m := Heap.HeapMApplyEquiv α m
    ⟨fun p : α → Heap.prop =>
      Heap.as_prop (fun h =>
        let (x, h') := m h
        (p x).1 h'),
      by
        intro p1 p2 h1 h h2 h' h3
        apply h1
        apply h2
        assumption
    ⟩

  bindθ := sorry
  pureθ := by
    intro α x

    apply Subtype.eq
    simp only

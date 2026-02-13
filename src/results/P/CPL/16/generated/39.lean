

theorem P1_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  unfold P1
  intro x hx
  have hsubset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    have hInner :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    exact closure_mono hInner
  exact hsubset hx
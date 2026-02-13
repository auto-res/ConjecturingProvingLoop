

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
  apply interior_maximal
  · exact subset_closure
  · exact isOpen_interior
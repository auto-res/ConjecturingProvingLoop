

theorem open_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal subset_closure hA
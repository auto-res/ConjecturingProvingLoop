

theorem Topology.open_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  simpa using interior_maximal subset_closure hA
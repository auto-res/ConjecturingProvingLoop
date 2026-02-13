

theorem Topology.open_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal subset_closure hA
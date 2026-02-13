

theorem Topology.subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : A ⊆ interior (closure A) := by
  simpa using
    (Topology.isOpen_implies_P3 (X := X) (A := A) hA)


theorem Topology.closure_inter_subset_closed_right {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hC : IsClosed C) :
    closure (A ∩ C) ⊆ C := by
  simpa [Set.inter_comm] using
    (Topology.closure_inter_subset_closed_left (X := X) (U := C) (A := A) hC)
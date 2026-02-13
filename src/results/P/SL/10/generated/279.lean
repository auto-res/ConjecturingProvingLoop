

theorem Topology.closure_union_closed_right {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hC : IsClosed C) :
    closure (A ∪ C) = closure A ∪ C := by
  have h :=
    Topology.closure_union_closed_left (X := X) (C := C) (A := A) hC
  simpa [Set.union_comm] using h
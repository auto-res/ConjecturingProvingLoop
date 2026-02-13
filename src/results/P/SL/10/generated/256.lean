

theorem Topology.closure_union_closed_left {X : Type*} [TopologicalSpace X]
    {C A : Set X} (hC : IsClosed C) :
    closure (C ∪ A) = C ∪ closure A := by
  simpa [hC.closure_eq] using (closure_union C A)


theorem Topology.closure_interior_minimal_closed
    {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hC : IsClosed C) (h_sub : interior A ⊆ C) :
    closure (interior A) ⊆ C := by
  have h₁ : closure (interior A) ⊆ closure C := closure_mono h_sub
  simpa [hC.closure_eq] using h₁
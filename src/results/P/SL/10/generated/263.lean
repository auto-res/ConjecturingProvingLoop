

theorem Topology.boundary_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    closure A \ interior A ⊆ A := by
  intro x hx
  rcases hx with ⟨hxCl, _hxNotInt⟩
  simpa [hClosed.closure_eq] using hxCl
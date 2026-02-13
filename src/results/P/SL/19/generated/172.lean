

theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  rcases hx with ⟨hx_clos, _⟩
  have hsubset : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  exact hsubset hx_clos


theorem Topology.frontier_eq_univ_diff_interior_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A → frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
  intro hDense
  have hCl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [frontier, hCl]
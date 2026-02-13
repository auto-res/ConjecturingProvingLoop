

theorem Topology.closureInterior_eq_univ_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → closure (interior A) = (Set.univ : Set X) := by
  intro hDense
  simpa using hDense.closure_eq


theorem Topology.denseInterior_implies_closureInterior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hDense
  simpa using hDense.closure_eq
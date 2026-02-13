

theorem Topology.denseInterior_iff_interiorClosureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔
      interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa using
    (Topology.dense_iff_interiorClosure_eq_univ (X := X) (A := interior A))
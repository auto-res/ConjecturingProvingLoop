

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx
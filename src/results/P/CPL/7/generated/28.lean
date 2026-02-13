

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx
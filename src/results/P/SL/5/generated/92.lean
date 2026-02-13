

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [closure_univ, interior_univ] using this
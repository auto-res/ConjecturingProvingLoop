

theorem Topology.denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (X := X) A := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  simpa [hDense.closure_eq, interior_univ] using
    (by
      simp : (x : X) ∈ (Set.univ : Set X))
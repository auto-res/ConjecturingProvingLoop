

theorem Topology.denseInterior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P1 (X := X) A := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  have h_cl : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_cl] using this
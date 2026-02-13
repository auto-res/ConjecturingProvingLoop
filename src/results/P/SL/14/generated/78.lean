

theorem Topology.closure_has_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hDense
  have h_eq : (closure (A : Set X) : Set X) = Set.univ := hDense.closure_eq
  dsimp [Topology.P1]
  intro x hx
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simpa [h_eq] using hx
  simpa [h_eq, interior_univ] using hx_univ
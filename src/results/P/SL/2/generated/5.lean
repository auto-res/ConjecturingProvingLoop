

theorem Topology.isOpen_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Dense A → Topology.P2 A := by
  intro hOpen hDense
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hOpen.interior_eq, hDense.closure_eq, interior_univ] using this
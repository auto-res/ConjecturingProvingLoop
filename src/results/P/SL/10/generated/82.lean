

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = Set.univ → Topology.P3 A := by
  intro h_dense
  dsimp [Topology.P3]
  intro x hxA
  have : (x : X) ∈ interior (closure A) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_dense, interior_univ] using this
  exact this


theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense] using this
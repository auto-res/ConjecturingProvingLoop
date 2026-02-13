

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = Set.univ) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hA] using this
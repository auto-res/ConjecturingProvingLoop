

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx_univ
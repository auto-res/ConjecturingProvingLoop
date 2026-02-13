

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  intro x _
  have : (x : X) ∈ interior (closure (interior (A : Set X))) := by
    simpa [hA, interior_univ] using (Set.mem_univ (x : X))
  exact this


theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h, interior_univ] using this
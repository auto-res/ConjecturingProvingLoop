

theorem dense_closure_satisfies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hDense] using (interior_univ : interior (Set.univ : Set X) = _)
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using this


theorem interior_closure_univ_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this
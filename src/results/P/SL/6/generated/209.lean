

theorem interior_closure_interior_eq_univ_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) →
      Topology.P2 (A : Set X) := by
  intro hUniv
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hUniv] using this
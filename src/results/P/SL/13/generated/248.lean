

theorem Topology.closureInterior_univ_implies_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this
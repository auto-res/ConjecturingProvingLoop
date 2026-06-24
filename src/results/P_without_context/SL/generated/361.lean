

theorem Topology.P3_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  intro x hx
  have hmem : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hcl
  exact hsubset hmem
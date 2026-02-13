

theorem P1_univ_iff_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P3 (Set.univ : Set X) := by
  have h₁ := Topology.P1_univ_iff_P2_univ (X := X)
  have h₂ := Topology.P3_univ_iff_P2_univ (X := X)
  simpa using h₁.trans h₂.symm
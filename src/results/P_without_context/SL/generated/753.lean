

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hA
  have h_sub : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact hA.trans h_sub
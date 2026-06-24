

theorem Topology.P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hP2.trans h₁
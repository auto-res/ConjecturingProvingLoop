

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hA
  have h₁ : interior (closure (interior (A : Set X))) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hA h₁
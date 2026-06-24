

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  have h₂ : interior (closure (interior (A : Set X))) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans h h₂
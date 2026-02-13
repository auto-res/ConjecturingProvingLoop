

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset (s := closure (interior A))
  exact Set.Subset.trans h h₁
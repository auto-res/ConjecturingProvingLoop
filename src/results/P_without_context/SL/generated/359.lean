

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro h
  have h₂ : interior (closure (interior (A : Set X))) ⊆ closure (interior A) := by
    simpa using interior_subset (s := closure (interior (A : Set X)))
  exact Set.Subset.trans h h₂
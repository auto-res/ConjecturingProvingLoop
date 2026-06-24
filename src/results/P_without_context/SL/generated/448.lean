

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans h h'
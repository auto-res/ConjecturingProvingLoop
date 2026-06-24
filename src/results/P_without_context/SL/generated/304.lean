

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  have h_sub : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact Set.Subset.trans h h_sub
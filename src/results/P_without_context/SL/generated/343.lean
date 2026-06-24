

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro h
  exact Set.Subset.trans h
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
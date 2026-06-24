

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro h
  unfold Topology.P2 Topology.P1 at *
  exact
    Set.Subset.trans h
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A))
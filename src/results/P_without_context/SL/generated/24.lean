

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (A := A) → Topology.P1 (X := X) (A := A) := by
  intro hA
  exact Set.Subset.trans hA interior_subset


theorem closure_interior_eq_of_closed_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply subset_antisymm
  ·
    have hIntSub : interior A ⊆ (A : Set X) := interior_subset
    exact closure_minimal hIntSub hA
  ·
    exact hP1
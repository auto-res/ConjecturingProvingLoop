

theorem interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  exact Topology.isOpen_implies_P1 (X := X) (A := interior A) isOpen_interior
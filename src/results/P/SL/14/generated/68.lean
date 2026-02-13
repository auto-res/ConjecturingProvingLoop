

theorem Topology.interior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  simpa using
    (Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := interior A) isOpen_interior)
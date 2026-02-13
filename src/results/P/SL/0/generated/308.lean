

theorem P3_iff_P1_and_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (A : Set X)) ↔
      (Topology.P1 (interior (A : Set X)) ∧ Topology.P2 (interior (A : Set X))) := by
  -- `interior A` is an open set.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Apply the already established equivalence for open sets.
  simpa using
    (Topology.P3_iff_P1_and_P2_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen)
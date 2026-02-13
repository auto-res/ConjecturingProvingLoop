

theorem Topology.isOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X := X) A := by
  -- Obtain `P2` for the open set `A`
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) hA
  -- From `P2` we immediately get `P1`
  exact (Topology.P2_implies_P1_and_P3 (X := X) (A := A) hP2).1


theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  -- First, dense interior implies `P2`.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- Since `P2` implies `P3`, we obtain the desired result.
  exact Topology.P2_implies_P3 (X := X) (A := A) hP2
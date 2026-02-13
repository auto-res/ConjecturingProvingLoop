

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A := by
  -- First, `A` satisfies `P2` because its interior is dense.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- Since `P2` implies `P1`, we obtain the desired result.
  exact Topology.P2_implies_P1 (X := X) (A := A) hP2
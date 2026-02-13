

theorem Topology.P2_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP2A : Topology.P2 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P2 (X := X) (A ∪ U) := by
  -- Any open set satisfies `P2`.
  have hP2U : Topology.P2 (X := X) U :=
    Topology.isOpen_implies_P2 (X := X) (A := U) hOpenU
  -- Apply the union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := U) hP2A hP2U
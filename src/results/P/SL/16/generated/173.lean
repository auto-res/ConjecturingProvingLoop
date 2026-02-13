

theorem Topology.P3_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP3A : Topology.P3 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P3 (X := X) (A ∪ U) := by
  -- An open set automatically satisfies `P3`.
  have hP3U : Topology.P3 (X := X) U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hOpenU
  -- Combine the two `P3` sets using the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := U) hP3A hP3U
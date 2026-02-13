

theorem P3_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → IsOpen (B : Set X) → Topology.P3 (A ∪ B) := by
  intro hP3A hOpenB
  -- An open set automatically satisfies `P3`.
  have hP3B : Topology.P3 B :=
    Topology.isOpen_implies_P3 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hP3A hP3B
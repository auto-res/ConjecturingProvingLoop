

theorem P1_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → IsOpen (B : Set X) → Topology.P1 (A ∪ B) := by
  intro hP1A hOpenB
  -- An open set automatically satisfies `P1`.
  have hP1B : Topology.P1 B :=
    Topology.isOpen_implies_P1 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P1`.
  exact Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B
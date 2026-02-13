

theorem P2_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → IsOpen (B : Set X) → Topology.P2 (A ∪ B) := by
  intro hP2A hOpenB
  -- An open set automatically satisfies `P2`.
  have hP2B : Topology.P2 B :=
    Topology.isOpen_implies_P2 (X := X) (A := B) hOpenB
  -- Combine the two sets using the existing union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := B) hP2A hP2B
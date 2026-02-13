

theorem P2_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hOpenA hP2B
  -- An open set automatically satisfies `P2`.
  have hP2A : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P2`.
  exact Topology.P2_union (X := X) (A := A) (B := B) hP2A hP2B
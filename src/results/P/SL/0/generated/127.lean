

theorem P1_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hOpenA hP1B
  -- An open set automatically satisfies `P1`.
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P1`.
  exact Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B
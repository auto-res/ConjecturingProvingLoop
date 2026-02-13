

theorem P3_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsOpen (A : Set X) → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hOpenA hP3B
  -- An open set automatically satisfies `P3`.
  have hP3A : Topology.P3 A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpenA
  -- Combine the two sets using the existing union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hP3A hP3B
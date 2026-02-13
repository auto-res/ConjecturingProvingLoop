

theorem Topology.P3_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 B := Topology.P3_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P3`.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B
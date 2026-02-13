

theorem Topology.P1_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hOpenB : IsOpen B) :
    Topology.P1 (A ∪ B) := by
  -- Obtain `P1` for `B` from its openness.
  have hP1B : Topology.P1 B := Topology.P1_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hP1A hP1B
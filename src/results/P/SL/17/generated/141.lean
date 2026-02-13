

theorem Topology.P2_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- Obtain `P2` for the open set `B`.
  have hP2B : Topology.P2 B := Topology.P2_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_union (A := A) (B := B) hP2A hP2B
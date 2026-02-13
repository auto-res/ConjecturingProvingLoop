

theorem P2_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- Obtain `P2` for the open set `B`.
  have hB : Topology.P2 B := Topology.P2_of_open (A := B) hB_open
  -- Apply the general union lemma for `P2`.
  exact Topology.P2_union (A := A) (B := B) hA hB


theorem P1_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ∪ B) := by
  -- Derive `P1` for the open set `B`.
  have hB : Topology.P1 B := Topology.P1_of_open (A := B) hB_open
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hA hB
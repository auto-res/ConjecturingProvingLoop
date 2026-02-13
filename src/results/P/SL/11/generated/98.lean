

theorem P3_union_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  -- Obtain `P3` for the open set `B`.
  have hB : Topology.P3 B := Topology.P3_of_open (A := B) hB_open
  -- Apply the general union lemma for `P3`.
  exact Topology.P3_union (A := A) (B := B) hA hB
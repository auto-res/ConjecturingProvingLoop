

theorem P1_union_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  -- Obtain `P1` for the open set `A`.
  have hA : Topology.P1 A := Topology.P1_of_open (A := A) hA_open
  -- Use the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hA hB
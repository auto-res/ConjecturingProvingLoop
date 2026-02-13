

theorem P3_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 (B : Set X) := Topology.P3_of_open hOpenB
  -- Combine the two `P3` properties.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B
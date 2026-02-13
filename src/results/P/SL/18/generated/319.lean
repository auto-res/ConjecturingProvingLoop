

theorem P3_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  -- The open set `A` itself satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) := Topology.P3_of_open hOpenA
  -- Combine the two `P3` properties.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B
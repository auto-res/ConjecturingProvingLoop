

theorem P3_union_of_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- An open set automatically satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) :=
    Topology.P3_of_isOpen (A := A) hA
  -- The union of two sets satisfying `P3` again satisfies `P3`.
  exact Topology.P3_union (A := A) (B := B) hP3A hB
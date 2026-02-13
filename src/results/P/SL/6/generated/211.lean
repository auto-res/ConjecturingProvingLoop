

theorem P3_union_of_P3_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 (B : Set X) :=
    Topology.open_satisfies_P3 (A := B) hOpenB
  -- Apply the existing union lemma for two sets satisfying `P3`.
  exact Topology.P3_union_of_P3 (A := A) (B := B) hP3A hP3B


theorem P1_union_of_P1_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  -- `B` is open, hence satisfies `P1`.
  have hP1B : Topology.P1 (B : Set X) :=
    Topology.open_satisfies_P1 (A := B) hOpenB
  -- Apply the union lemma for two sets satisfying `P1`.
  exact Topology.P1_union_of_P1 (A := A) (B := B) hP1A hP1B


theorem Topology.P1_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  -- Swap the roles of `A` and `B` and apply the existing lemma.
  have h :=
    Topology.P1_union_right_of_open (X := X) (A := B) (B := A) hPB hA_open
  simpa [Set.union_comm] using h
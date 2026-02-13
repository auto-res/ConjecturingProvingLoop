

theorem Topology.P3_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Apply the “right” version with the roles of `A` and `B` swapped,
  -- then rewrite using commutativity of `∪`.
  have h :=
    Topology.P3_union_right_of_open (X := X) (A := B) (B := A) hPB hA_open
  simpa [Set.union_comm] using h
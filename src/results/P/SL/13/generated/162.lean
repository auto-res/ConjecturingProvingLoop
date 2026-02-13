

theorem Topology.P2_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P2 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- Apply the “left” version with the roles of `A` and `B` swapped,
  -- then rewrite using commutativity of `∩`.
  have h :=
    Topology.P2_inter_left_of_open (X := X) (A := B) (B := A) hB_open hPA
  simpa [Set.inter_comm] using h
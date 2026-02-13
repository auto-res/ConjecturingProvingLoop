

theorem P2_inter_of_open_and_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Apply the existing lemma with the factors swapped, then rewrite.
  have h :=
    Topology.P2_inter_of_P2_and_open (A := B) (B := A) hP2B hOpenA
  simpa [Set.inter_comm] using h


theorem Topology.P1_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  -- Apply the existing lemma with swapped roles and rewrite the intersection.
  have h := Topology.P1_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.inter_comm] using h
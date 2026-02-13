

theorem Topology.P3_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Reuse the existing lemma with the roles of `A` and `B` swapped.
  have h : Topology.P3 (B ∩ A) :=
    Topology.P3_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.inter_comm] using h
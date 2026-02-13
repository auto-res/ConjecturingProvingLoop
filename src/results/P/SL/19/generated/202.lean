

theorem Topology.interior_inter_eq_inter_right_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- Apply the existing lemma with the factors swapped.
  have h :=
    Topology.interior_inter_eq_inter_left_of_isOpen_right
      (A := B) (B := A) hA
  simpa [Set.inter_comm] using h
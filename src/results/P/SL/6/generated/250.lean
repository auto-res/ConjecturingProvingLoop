

theorem interior_inter_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ interior B := by
  simpa [Set.inter_comm] using
    (interior_inter_of_isOpen_right (A := B) (B := A) hA)
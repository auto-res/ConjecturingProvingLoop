

theorem interior_inter_left_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  simpa [Set.inter_comm] using
    (interior_inter_right_open (A := B) (B := A) hA)
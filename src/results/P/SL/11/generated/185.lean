

theorem interior_inter_eq_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).interior_eq
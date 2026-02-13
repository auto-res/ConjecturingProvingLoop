

theorem interior_inter_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq
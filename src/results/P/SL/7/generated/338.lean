

theorem interior_inter_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∩ B ∩ C : Set X) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C : Set X) := by
    have hAB : IsOpen (A ∩ B : Set X) := hA.inter hB
    exact hAB.inter hC
  simpa using hOpen.interior_eq
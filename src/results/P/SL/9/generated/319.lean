

theorem interior_inter_left_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B) = interior A ∩ B := by
  have h := Topology.interior_inter_eq_inter (A := A) (B := B)
  simpa [hB.interior_eq] using h
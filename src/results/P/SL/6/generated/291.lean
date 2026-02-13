

theorem interior_diff_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed (B : Set X)) :
    interior ((A \ B) : Set X) = interior A \ B := by
  have hOpenComp : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
  simpa [Set.diff_eq] using
    (interior_inter_of_isOpen_right (A := A) (B := Bᶜ) hOpenComp)
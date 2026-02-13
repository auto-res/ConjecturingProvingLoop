

theorem frontier_subset_compl_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    frontier (A : Set X) ⊆ Aᶜ := by
  have h := frontier_subset_compl_interior (X := X) (A := A)
  simpa [hA.interior_eq] using h
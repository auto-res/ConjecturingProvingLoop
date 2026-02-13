

theorem interior_subset_of_subset_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : IsOpen B) :
    interior A ⊆ B := by
  intro x hxIntA
  exact hAB (interior_subset hxIntA)
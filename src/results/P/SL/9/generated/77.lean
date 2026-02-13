

theorem closure_diff_subset_of_isOpen {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hT : IsOpen t) :
    closure (s \ t) ⊆ closure s \ t := by
  have h := closure_diff_subset (s) (t)
  simpa [hT.interior_eq] using h
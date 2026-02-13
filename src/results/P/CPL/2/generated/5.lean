

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 (X := X) A := by
  unfold P1
  simpa [hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)
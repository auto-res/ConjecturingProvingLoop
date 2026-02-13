

theorem interior_closure_subset_of_subset_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : IsClosed B) :
    interior (closure A) ⊆ B := by
  intro x hxInt
  have hclosure : closure A ⊆ B := by
    have h : closure A ⊆ closure B := closure_mono hAB
    simpa [hB.closure_eq] using h
  exact hclosure (interior_subset hxInt)
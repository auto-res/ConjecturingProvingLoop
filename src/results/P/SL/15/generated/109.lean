

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  exact interior_mono h_closure
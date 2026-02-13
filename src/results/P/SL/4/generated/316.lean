

theorem closure_inter_closure_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  have h :=
    closure_inter_subset_inter_closure
      (A := A) (B := closure B)
  simpa [closure_closure] using h
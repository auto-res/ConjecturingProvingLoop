

theorem boundary_of_isClosed_eq_inter_closure_complement {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) =
      (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  have h := boundary_eq_closure_inter_closure_compl (A := A)
  simpa [hA.closure_eq] using h
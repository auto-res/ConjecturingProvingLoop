

theorem closure_inter_closure_compl_of_closureInterior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ closure ((interior (A : Set X))ᶜ) =
      closure (interior (A : Set X)) \ interior A := by
  simpa [interior_interior] using
    (closure_inter_closure_compl_eq_closure_diff_interior
      (X := X) (A := interior (A : Set X)))
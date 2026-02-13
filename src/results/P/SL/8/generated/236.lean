

theorem denseInterior_imp_closureInteriorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure (interior (closure A)) = closure A := by
  -- From the density assumption we get `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- And we also have `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) :=
    interior_closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Rewrite both sides using these identities.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int_univ]
    _ = (Set.univ : Set X) := by
          simpa [closure_univ]
    _ = closure A := by
          simpa [h_closure_univ]
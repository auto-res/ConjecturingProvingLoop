

theorem interior_closure_eq_univ_of_denseInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- First, obtain `closure A = univ` from the existing lemma.
  have h_closure : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Rewrite and conclude.
  calc
    interior (closure A)
        = interior (Set.univ : Set X) := by
          simpa [h_closure]
    _ = (Set.univ : Set X) := by
          simpa [interior_univ]
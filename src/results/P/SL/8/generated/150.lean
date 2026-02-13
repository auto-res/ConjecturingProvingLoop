

theorem closed_P3_imp_closureInterior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- First, use the existing lemma to get `interior A = A`.
  have hInt : interior A = A :=
    closed_P3_interior_eq (X := X) (A := A) hA_closed hP3
  -- Rewrite and use that `A` is closed, so `closure A = A`.
  simpa [hInt, hA_closed.closure_eq]
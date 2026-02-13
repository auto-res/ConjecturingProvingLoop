

theorem interior_closure_eq_self_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, `P3` together with closedness gives `interior A = A`.
  have hInt : interior (A : Set X) = A :=
    interior_eq_self_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- For closed sets, `interior (closure A) = interior A`.
  have hIntCl : interior (closure (A : Set X)) = interior (A : Set X) :=
    interior_closure_eq_interior_of_isClosed (A := A) hA_closed
  -- Combine the two equalities.
  simpa [hInt] using hIntCl
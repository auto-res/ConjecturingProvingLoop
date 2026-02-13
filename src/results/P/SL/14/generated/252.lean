

theorem Topology.closureInterior_eq_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = (A : Set X) := by
  -- From `P3` and closedness we have `interior A = A`.
  have h_int_eq : interior A = (A : Set X) :=
    Topology.interior_eq_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  -- Hence `closure (interior A) = closure A`.
  have h_cl_eq : closure (interior A) = closure (A : Set X) := by
    simpa [h_int_eq]
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using h_cl_eq


theorem closure_eq_univ_of_P1_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDenseInt : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  -- From `P1`, we know `closure A = closure (interior A)`.
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Since `interior A` is dense, its closure is the whole space.
  have h_univ : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDenseInt.closure_eq
  -- Combining the two equalities yields the result.
  simpa [h_univ] using h_cl_eq
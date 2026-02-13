

theorem closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hDense : Dense A) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1`, we have `closure A = closure (interior A)`.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Combining the two equalities yields the desired result.
  simpa [h_closure_eq] using h_closure_univ
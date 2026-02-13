

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, shorten the goal using the existing 3-fold contraction lemma
  have h1 :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior
        (A := closure (interior A)))
  -- Next, contract once more using the 2-fold lemma
  have h2 :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior (A := A))
  -- Combine the two equalities to obtain the desired result
  simpa [h2] using h1
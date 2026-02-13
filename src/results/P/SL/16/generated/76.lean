

theorem Topology.interior_closure_interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First, simplify the innermost pattern using the existing lemma with
  -- `A := closure (interior A)`.
  have h₁ :
      interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
        (X := X) (A := closure (interior A)))
  -- Next, collapse the remaining expression once more with `A := A`.
  have h₂ :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
        (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁
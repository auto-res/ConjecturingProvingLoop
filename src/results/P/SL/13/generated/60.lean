

theorem Topology.closure_interior_closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- First, collapse the innermost five-layer expression using the existing lemma
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (interior (closure A)))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := interior (closure (A : Set X))))
  -- Next, collapse the resulting three-layer expression using the same lemma
  have h₂ :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := A))
  -- Combine the two equalities
  calc
    closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (interior (closure A)))) := by
          simpa using h₁
    _ = closure (interior (closure A)) := by
          simpa using h₂
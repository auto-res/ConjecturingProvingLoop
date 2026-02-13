

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure (A : Set X)) := by
  -- First, collapse the innermost six-layer expression to a four-layer one.
  have h₁ :
      interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (A := interior (closure (A : Set X))))
  -- Next, collapse the resulting four-layer expression to the desired two-layer one.
  have h₂ :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (A := A))
  -- Combine the two equalities.
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := h₁
    _ = interior (closure (A : Set X)) := h₂
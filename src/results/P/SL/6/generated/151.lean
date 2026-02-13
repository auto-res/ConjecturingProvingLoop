

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (A : Set X))))))))) =
      closure (interior (closure A)) := by
  -- Step 1: Reduce the innermost seven-layer pattern to the canonical form.
  have h₁ :
      closure
        (interior
          (closure
            (interior
              (closure (interior (closure A)))))) =
        closure (interior (closure A)) := by
    simpa using
      (closure_interior_closure_interior_closure_interior_closure_eq (A := A))
  -- Step 2: Substitute `h₁` and finish with the five-layer equality lemma.
  calc
    closure
        (interior
          (closure
            (interior
              (closure (interior (closure (interior (closure A)))))))) =
        closure (interior (closure (interior (closure A)))) := by
          simpa [h₁]
    _ = closure (interior (closure A)) := by
          simpa using
            (closure_interior_closure_interior_closure_eq (A := A))
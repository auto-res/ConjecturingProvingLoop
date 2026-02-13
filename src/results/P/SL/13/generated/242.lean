

theorem Topology.closure_interior_iterate_nine_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior
      (closure (interior
        (closure (interior
          (closure (interior
            (closure (interior
              (closure (interior (A : Set X))))
            ))
          ))
        )))) =
      closure (interior A) := by
  -- Collapse the innermost eight-layer expression.
  have h₁ :=
    Topology.closure_interior_iterate_eight_eq_closure_interior
      (X := X) (A := A)
  -- Rewrite using `h₁` and apply the two-layer idempotency lemma.
  calc
    closure (interior
      (closure (interior
        (closure (interior
          (closure (interior
            (closure (interior
              (closure (interior (A : Set X))))
            ))
          ))
        )))) =
        closure (interior (closure (interior A))) := by
          simpa [h₁]
    _ = closure (interior A) := by
          simpa using
            (Topology.closure_interior_closure_interior_eq_closure_interior
              (X := X) (A := A))
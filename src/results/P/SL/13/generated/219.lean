

theorem Topology.interior_closure_iterate_ten_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure (A : Set X))))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost nine-layer expression using the existing lemma.
  have h₁ :=
    Topology.interior_closure_iterate_nine_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two-layer idempotency lemma.
  simpa [h₁,
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)]
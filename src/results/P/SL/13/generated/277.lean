

theorem Topology.interior_closure_iterate_fourteen_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
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
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost thirteen‐layer expression.
  have h :=
    Topology.interior_closure_iterate_thirteen_eq_interior_closure
      (X := X) (A := A)
  -- Rewrite using `h`, then simplify via the two‐layer idempotency lemma.
  simpa [h,
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)]
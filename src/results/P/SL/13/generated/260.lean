

theorem Topology.interior_closure_iterate_thirteen_eq_interior_closure {X : Type*}
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
  -- Collapse the innermost twelve‐layer expression using the existing lemma.
  have h :=
    Topology.interior_closure_iterate_twelve_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two‐layer idempotency lemma.
  simpa [h,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]
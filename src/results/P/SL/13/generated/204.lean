

theorem Topology.interior_closure_iterate_nine_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
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
      )) =
      interior (closure A) := by
  -- First, collapse the innermost eight-layer expression using the existing lemma.
  have h8 :=
    Topology.interior_closure_iterate_eight_eq_interior_closure (X := X) (A := A)
  -- After rewriting with `h8`, we are left with `interior (closure (interior (closure A)))`,
  -- which simplifies via the two-layer idempotency lemma.
  simpa [h8,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]
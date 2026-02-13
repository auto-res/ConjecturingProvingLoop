

theorem Topology.interior_closure_iterate_eleven_eq_interior_closure {X : Type*}
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
  -- First, collapse the innermost ten-layer expression using the existing lemma.
  have h₁ :=
    Topology.interior_closure_iterate_ten_eq_interior_closure (X := X) (A := A)
  -- Rewrite the goal using `h₁`, then finish with the two-layer idempotency lemma.
  calc
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
        interior (closure (interior (closure A))) := by
          simpa [h₁]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))
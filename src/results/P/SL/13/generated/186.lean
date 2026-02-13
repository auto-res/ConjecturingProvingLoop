

theorem Topology.interior_closure_iterate_seven_eq_interior_closure {X : Type*}
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
  -- Repeatedly simplify using the idempotency of `interior ∘ closure`.
  simp [Topology.interior_closure_interior_closure_eq_interior_closure (X := X)]
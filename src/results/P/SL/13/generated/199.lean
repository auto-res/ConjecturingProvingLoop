

theorem Topology.interior_closure_iterate_eight_eq_interior_closure {X : Type*}
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
  simp
    [Topology.interior_closure_iterate_seven_eq_interior_closure (X := X) (A := A),
     Topology.interior_closure_interior_closure_eq_interior_closure (X := X) (A := A)]
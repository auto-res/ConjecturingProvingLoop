

theorem P1_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hEq : closure A = interior A) : Topology.P1 (X:=X) A := by
  unfold Topology.P1
  intro x hx
  -- `x` is in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  -- Relate the two closures using the given equality
  have h_cl_eq : closure (interior (A : Set X)) = closure A := by
    calc
      closure (interior (A : Set X))
          = closure (closure A) := by
            simpa [hEq]
      _ = closure A := by
        simpa [closure_closure]
  -- Rewrite and conclude
  simpa [h_cl_eq] using hx_cl


theorem interior_closure_eq_interior_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure (A : Set X)))) := by
  -- `P3` gives a closure equality involving `A` and `interior (closure A)`.
  have hClos :
      closure (A : Set X) = closure (interior (closure (A : Set X))) :=
    Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3
  -- Applying `interior` to both sides yields the desired result.
  simpa using congrArg (fun s : Set X => interior s) hClos
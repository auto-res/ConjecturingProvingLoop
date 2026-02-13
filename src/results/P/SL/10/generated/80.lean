

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP1
  -- Step 1: obtain the equality of interiors of closures from `P1`.
  have h_int_eq :=
    Topology.interior_closure_eq_of_P1 (X := X) (A := A) hP1
  -- Step 2: apply `closure` to both sides of the equality.
  have h_closure_eq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) :=
    congrArg (fun s : Set X => closure s) h_int_eq
  -- Step 3: use the idempotent property to rewrite the right–hand side.
  have h_target :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Step 4: conclude by combining the two equalities.
  simpa [h_target] using h_closure_eq
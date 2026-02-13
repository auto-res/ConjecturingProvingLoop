

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- Step 1: obtain the equality of interiors provided by `P2`.
  have h_int_eq :=
    Topology.interior_closure_eq_of_P2 (X := X) (A := A) hP2
  -- Step 2: apply `closure` to both sides of the equality.
  have h_cl_eq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) :=
    congrArg (fun s : Set X => closure s) h_int_eq
  -- Step 3: simplify the right–hand side using the idempotent property.
  have h_simp :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Step 4: conclude by rewriting.
  simpa [h_simp] using h_cl_eq
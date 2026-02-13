

theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- Apply `closure` to both sides of the interior-level equality and simplify.
  have h :=
    congrArg (fun s : Set X => closure s)
      (interior_closure_interior_closure_interior_closure_eq (A := A))
  simpa using h
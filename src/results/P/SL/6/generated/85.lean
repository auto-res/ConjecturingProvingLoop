

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure A)) := by
  -- Use the previously established equality for the inner term.
  have h :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure A) :=
    interior_closure_interior_closure_eq (A := A)
  -- Apply `closure` to both sides.
  simpa using congrArg closure h
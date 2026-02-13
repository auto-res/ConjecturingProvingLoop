

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  -- Use the previously established eight-step idempotence.
  have h :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior A) :=
    closure_interior_closure_interior_closure_interior_closure_interior_eq
      (X := X) (A := A)
  -- Apply `closure ∘ interior` to both sides of `h`.
  simpa using congrArg (fun S : Set X => closure (interior S)) h
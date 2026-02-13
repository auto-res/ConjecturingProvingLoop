

theorem closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- Step 1: the basic two-step idempotence.
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (closure_interior_closure_interior_eq
        (X := X) (A := A))
  -- Step 2: apply `closure ∘ interior` to both sides of `h₁`.
  have h₂ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      congrArg (fun S : Set X => closure (interior S)) h₁
  -- Step 3: simplify the right-hand side with `h₁`.
  simpa [h₁] using h₂


theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, collapse three inner `closure ∘ interior` pairs.
  have h₁ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) :=
    closure_interior_closure_interior_closure_interior_eq (X := X) (A := A)
  -- Apply `closure ∘ interior` once more to both sides of `h₁`.
  have h₂ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun S : Set X => closure (interior S)) h₁
  -- Finally, collapse the remaining pair.
  have h₃ : closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_eq (X := X) (A := A)
  simpa [h₃] using h₂
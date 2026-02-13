

theorem interior_closure_eq_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) = closure (B : Set X) →
      interior (closure (A : Set X)) = interior (closure (B : Set X)) := by
  intro h
  simpa using congrArg interior h
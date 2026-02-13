

theorem closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
      closure (interior (A : Set X)) := by
  -- Reuse the basic idempotence lemma twice.
  have h₁ :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior (A : Set X)) :=
    Topology.closure_interior_closure_interior_idempotent (X := X) (A := A)
  calc
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
        closure (interior (closure (closure (interior (A : Set X))))) := by
          simpa [h₁]
    _ = closure (interior (closure (interior (A : Set X)))) := by
          simpa [closure_closure]
    _ = closure (interior (A : Set X)) := by
          simpa [h₁]
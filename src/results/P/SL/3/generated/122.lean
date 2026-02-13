

theorem closure_eq_closure_interior_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) =
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- `closure A = closure (interior A)` via `P1`
  have h₁ := closure_eq_closure_interior_of_P1 (A := A) hP1
  -- `closure (interior (closure A)) = closure (interior A)` via `P1`
  have h₂ := closure_interior_closure_eq_closure_interior_of_P1 (A := A) hP1
  calc
    closure (A : Set X)
        = closure (interior (A : Set X)) := h₁
    _ = closure (interior (closure (A : Set X))) := by
        simpa using h₂.symm
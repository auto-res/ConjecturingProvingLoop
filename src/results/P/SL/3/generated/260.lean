

theorem closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hP2
  have h₁ :=
    closure_interior_closure_eq_closure_interior_of_P2 (A := A) hP2
  have h₂ := closure_eq_closure_interior_of_P2 (A := A) hP2
  calc
    closure (interior (closure (A : Set X)))
        = closure (interior (A : Set X)) := h₁
    _ = closure (A : Set X) := by
          simpa using h₂.symm


theorem Topology.closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP2
  have h₁ :
      closure (interior (closure A)) = closure (interior A) :=
    Topology.closure_interior_closure_eq_closure_interior_of_P2 (A := A) hP2
  have h₂ : closure (interior A) = closure A :=
    (Topology.closure_eq_closure_interior_of_P2 (A := A) hP2).symm
  calc
    closure (interior (closure A))
        = closure (interior A) := h₁
    _ = closure A := h₂
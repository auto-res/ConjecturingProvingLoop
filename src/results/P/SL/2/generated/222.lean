

theorem Topology.P2_implies_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- From `P2`, we know both `closure (interior (closure A)) = closure A`
  -- and `closure (interior A) = closure A`.
  have h₁ :=
    Topology.P2_implies_closure_interior_closure_eq_closure (A := A) hP2
  have h₂ :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Rearrange `h₂` to match the direction needed for the calculation.
  have h₃ : closure A = closure (interior A) := by
    simpa using h₂.symm
  calc
    closure (interior (closure A)) = closure A := h₁
    _ = closure (interior A) := h₃
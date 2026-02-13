

theorem Topology.closure_interior_closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (closure (interior A))) = closure A := by
  intro hP2
  -- From `P2` we have `closure A = closure (interior A)`.
  have h₁ : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  -- The nested `closure ∘ interior` expression contracts to `closure (interior A)`.
  have h₂ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Combine the two equalities.
  simpa [h₁] using h₂
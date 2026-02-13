

theorem Topology.closure_interior_closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A →
      closure (interior (closure (interior A))) = closure A := by
  intro hP2
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  have h₂ : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (X := X) (A := A) hP2
  simpa [h₂] using h₁


theorem Topology.P1_implies_closureInteriorClosureInterior_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A →
      closure (interior (closure (interior (A : Set X)))) = closure (A : Set X) := by
  intro hP1
  -- First, collapse the nested `closure ∘ interior` expression.
  have h₁ :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)
  -- Next, identify `closure (interior A)` with `closure A` using `P1`.
  have h₂ :
      closure (interior (A : Set X)) = closure (A : Set X) := by
    simpa using
      ((Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1).symm
  -- Combine the two equalities.
  simpa [h₂] using h₁
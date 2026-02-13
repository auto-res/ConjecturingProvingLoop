

theorem Topology.closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) → closure (interior (closure A)) = closure A := by
  intro hP1
  -- First, rewrite `closure (interior (closure A))` using `P1`.
  have h₁ :=
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Secondly, `P1` identifies `closure A` with `closure (interior A)`.
  have h₂ :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Combine the two equalities.
  calc
    closure (interior (closure A))
        = closure (interior A) := h₁
    _ = closure A := by
          simpa using h₂.symm
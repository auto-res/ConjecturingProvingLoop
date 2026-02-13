

theorem Topology.closure_eq_closure_interior_closure_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior (closure A)) := by
  intro hP1
  -- First, rewrite `closure A` using `P1`.
  have h₁ :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Next, relate the two closures of interiors via `P1`.
  have h₂ :=
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Chain the equalities together.
  calc
    closure A = closure (interior A) := h₁
    _ = closure (interior (closure A)) := h₂.symm
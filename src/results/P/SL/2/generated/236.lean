

theorem Topology.P1_implies_closure_interior_closure_eq_closure_interior_simple
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (closure (A : Set X))) = closure (interior A) := by
  intro hP1
  -- First, rewrite `closure (interior (closure A))` using `P1 A`.
  have h₁ := Topology.P1_implies_closure_interior_closure_eq_closure (A := A) hP1
  -- Next, rewrite `closure A` in terms of `closure (interior A)`.
  have h₂ := Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  simpa [h₂.symm] using h₁


theorem open_closure_interior_iff_open_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      (IsOpen (closure (interior (A : Set X))) ↔ IsOpen (closure A)) := by
  intro hP2
  -- From `P2`, the two closures coincide.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Trivial equivalence, rewritten using `hEq`.
  have h : IsOpen (closure (interior (A : Set X)))
      ↔ IsOpen (closure (interior (A : Set X))) := Iff.rfl
  simpa [hEq] using h
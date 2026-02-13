

theorem Topology.interior_eq_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior A = closure A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- From the hypothesis we know that `A` is both open and closed.
  have hOpen : IsOpen A :=
    (Topology.open_and_closed_of_interior_eq_closure (X := X) (A := A) h).1
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen


theorem Topology.P2_iff_P3_of_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior A) = closure A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- Obtain `P1 A` from the given closure equality.
  have hP1 : Topology.P1 A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq
  -- Use the existing equivalence `P2 A ↔ P1 A ∧ P3 A`.
  have hEquiv := (Topology.P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2
  · intro hP3
    have : Topology.P1 A ∧ Topology.P3 A := And.intro hP1 hP3
    exact (hEquiv).2 this


theorem Topology.P2_iff_P3_of_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    -- Extract `P3 A` from the existing equivalence.
    have h := (Topology.P2_iff_P3_and_interior_closure_eq (A := A)).1 hP2
    exact h.1
  · intro hP3
    -- Build `P2 A` using the provided equality.
    exact
      Topology.P2_of_P3_and_interior_closure_eq
        (A := A) hP3 hEq
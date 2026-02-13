

theorem Topology.P2_closure_interior_of_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (X := X) (closure (interior A)) := by
  -- Use the equivalence previously established for closed sets.
  have h_equiv :=
    Topology.P2_closure_interior_iff_isOpen_closure_interior (X := X) (A := A)
  exact h_equiv.mpr h_open
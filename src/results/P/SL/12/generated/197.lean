

theorem Topology.P2_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P2 (X := X) (closure A) := by
  have h_equiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  exact h_equiv.mpr h_open
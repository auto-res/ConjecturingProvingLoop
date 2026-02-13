

theorem Topology.P2_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure A)) :
    Topology.P2 (X := X) (closure A) := by
  -- Use the equivalence between `P2` and `P3` for closed sets.
  exact
    ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).symm).mp h
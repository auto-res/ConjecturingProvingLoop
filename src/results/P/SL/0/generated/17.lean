

theorem closure_interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  -- `interior (closure A)` is open, hence it satisfies `P1`.
  have hP1_int : Topology.P1 (interior (closure A)) := by
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    exact (Topology.isOpen_has_all_Ps (X := X) (A := interior (closure A)) hOpen).1
  -- Property `P1` is preserved under taking closures.
  exact (Topology.P1_implies_P1_closure (X := X) (A := interior (closure A))) hP1_int
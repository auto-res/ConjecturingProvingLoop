

theorem Topology.P3_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  have h_open : IsOpen (closure A) :=
    ((Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).1) hP2
  exact Topology.P3_of_isOpen_closure (X := X) (A := A) h_open
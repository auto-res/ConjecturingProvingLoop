

theorem Topology.P1_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hP3
  have hOpen : IsOpen (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1 hP3
  exact Topology.isOpen_implies_P1 (X := X) (A := closure A) hOpen
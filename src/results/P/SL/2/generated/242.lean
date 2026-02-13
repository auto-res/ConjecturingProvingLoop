

theorem Topology.isOpen_closure_implies_P1_P2_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      (Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) := by
  intro hOpen
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.isOpen_closure_implies_P1_closure (A := A) hOpen
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    Topology.isOpen_closure_implies_P2_closure (A := A) hOpen
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact And.intro hP1 (And.intro hP2 hP3)
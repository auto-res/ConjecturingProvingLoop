

theorem open_closure_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X))
      ∧ Topology.P2 (closure A)
      ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    open_closure_implies_P1_closure (A := A) hOpen
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    open_closure_implies_P2_closure (A := A) hOpen
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    Topology.open_satisfies_P3 (A := closure (A : Set X)) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)
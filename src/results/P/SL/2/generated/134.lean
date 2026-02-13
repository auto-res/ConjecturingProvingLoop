

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P1 (closure (A : Set X)) := by
  intro hOpen
  have hP1A : Topology.P1 (A : Set X) :=
    Topology.isOpen_implies_P1 (A := A) hOpen
  exact Topology.P1_closure_of_P1 (A := A) hP1A
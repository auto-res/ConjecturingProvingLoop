

theorem isOpen_closure_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  intro hOpen
  have hP1 := P1_closure_of_isOpen_closure (X := X) (A := A) hOpen
  have hP2 := P2_of_isOpen_closure (X := X) (A := A) hOpen
  have hP3 := P3_closure_of_isOpen_closure (X := X) (A := A) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)
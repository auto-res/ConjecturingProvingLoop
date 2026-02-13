

theorem isOpen_closure_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen (closure A)) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    isOpen_closure_imp_P1 (X := X) (A := A) h_open
  have hP2 : Topology.P2 (closure A) :=
    isOpen_closure_imp_P2_closure (X := X) (A := A) h_open
  have hP3 : Topology.P3 (closure A) :=
    isOpen_closure_imp_P3_closure (X := X) (A := A) h_open
  exact And.intro hP1 (And.intro hP2 hP3)


theorem Topology.P2_and_P3_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP2 : Topology.P2 (closure A) :=
    (Topology.P2_of_isOpen_closure (X := X) (A := A)) h_open
  have hP3 : Topology.P3 (closure A) :=
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).2) h_open
  exact ⟨hP2, hP3⟩
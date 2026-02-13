

theorem isClosed_imp_P1_P2_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hP1 : Topology.P1 (Aᶜ) :=
    isClosed_imp_P1_compl (X := X) (A := A) hA_closed
  have hP2 : Topology.P2 (Aᶜ) :=
    isClosed_imp_P2_compl (X := X) (A := A) hA_closed
  have hP3 : Topology.P3 (Aᶜ) :=
    isClosed_imp_P3_compl (X := X) (A := A) hA_closed
  exact And.intro hP1 (And.intro hP2 hP3)
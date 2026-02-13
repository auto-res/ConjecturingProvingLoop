

theorem denseInterior_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_imp_P1 (X := X) (A := A) h_dense
  have hP2 : Topology.P2 A :=
    Topology.denseInterior_imp_P2 (X := X) (A := A) h_dense
  have hP3 : Topology.P3 A :=
    Topology.denseInterior_imp_P3 (X := X) (A := A) h_dense
  exact And.intro hP1 (And.intro hP2 hP3)
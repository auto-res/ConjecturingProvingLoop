

theorem denseInterior_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    denseInterior_imp_P1_closure (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (closure A) :=
    denseInterior_imp_P2_closure (X := X) (A := A) h_dense
  have hP3 : Topology.P3 (closure A) :=
    denseInterior_imp_P3_closure (X := X) (A := A) h_dense
  exact And.intro hP1 (And.intro hP2 hP3)
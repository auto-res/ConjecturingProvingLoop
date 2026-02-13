

theorem Topology.P2_nonempty_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  exact Topology.P1_nonempty_closureInterior (X := X) (A := A) hP1 hA
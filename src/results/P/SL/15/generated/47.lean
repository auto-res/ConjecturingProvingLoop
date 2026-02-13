

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP2 hA
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact
    Topology.interior_closure_nonempty_of_P3 (X := X) (A := A) hP3 hA
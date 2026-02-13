

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → Topology.P2 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact interior_closure_nonempty_of_P3 (A := A) hA hP3
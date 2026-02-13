

theorem Topology.P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) → Topology.P3 (X := X) A := by
  intro hP2cl
  -- From P2 for `closure A`, we obtain P3 for `closure A`.
  have hP3cl : Topology.P3 (X := X) (closure (A : Set X)) :=
    Topology.P2_implies_P3 (X := X) (A := closure A) hP2cl
  -- P3 for `closure A` implies P3 for `A`.
  exact Topology.P3_closure_implies_P3 (X := X) (A := A) hP3cl
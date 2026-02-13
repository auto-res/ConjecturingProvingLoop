

theorem P3_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP3_cl
  -- First upgrade `P3` to `P2` using the existing lemma.
  have hP2_cl : Topology.P2 (closure (A : Set X)) :=
    (Topology.P3_closure_implies_P2_closure (X := X) (A := A)) hP3_cl
  -- Then upgrade `P2` to `P1` using another existing lemma.
  exact (Topology.P2_closure_implies_P1_closure (X := X) (A := A)) hP2_cl
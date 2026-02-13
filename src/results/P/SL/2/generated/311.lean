

theorem Topology.P2_union_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B →
      closure (interior (closure (A ∪ B))) = closure (A ∪ B) := by
  intro hP2A hP2B
  have hP3A : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2A
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 (A := B) hP2B
  exact
    Topology.P3_union_implies_closure_interior_closure_eq_closure
      (A := A) (B := B) hP3A hP3B
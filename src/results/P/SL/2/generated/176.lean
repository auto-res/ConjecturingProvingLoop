

theorem Topology.P3_union_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B →
      closure (interior (closure (A ∪ B))) = closure (A ∪ B) := by
  intro hP3A hP3B
  have hP3Union : Topology.P3 (A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hP3A hP3B
  exact
    Topology.P3_implies_closure_interior_closure_eq_closure
      (A := A ∪ B) hP3Union
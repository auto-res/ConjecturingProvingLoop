

theorem Topology.closure_eq_closure_interior_union_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := B) →
      closure (A ∪ B) = closure (interior (A ∪ B)) := by
  intro hA hB
  have hA_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hA
  have hB_eq : closure B = closure (interior B) :=
    Topology.closure_eq_closure_interior_of_P1 (A := B) hB
  exact
    Topology.closure_eq_closure_interior_union
      (A := A) (B := B) hA_eq hB_eq
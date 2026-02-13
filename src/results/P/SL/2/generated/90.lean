

theorem Topology.P1_union_implies_closure_interior_eq_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      closure (interior (A ∪ B)) = closure (A ∪ B) := by
  intro hP1A hP1B
  -- First, `A ∪ B` satisfies `P1` by the corresponding union lemma.
  have hP1Union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hP1A hP1B
  -- Apply the characterization of `P1` in terms of closures.
  exact
    Topology.P1_implies_closure_interior_eq_closure
      (A := A ∪ B) hP1Union
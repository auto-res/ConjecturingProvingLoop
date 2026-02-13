

theorem Topology.closure_eq_closure_interior_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      closure (A ∪ B) = closure (interior (A ∪ B)) := by
  intro hA hB
  -- Obtain `P1` for the union from the hypotheses on `A` and `B`.
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Translate `P1` for the union into the desired equality of closures.
  exact Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := A ∪ B) hUnion
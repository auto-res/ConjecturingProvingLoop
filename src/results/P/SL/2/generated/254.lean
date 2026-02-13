

theorem Topology.P2_of_P3_and_closure_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A ⊆ closure (interior A) → Topology.P2 A := by
  intro hP3 hClSub
  -- From the assumptions, obtain `P1 A` using the existing lemma.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_P3_and_closure_subset (A := A) hP3 hClSub
  -- Combine `P1 A` and `P3 A` to deduce `P2 A`.
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3


theorem P1_closure_iUnion_of_P1
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P1 (S i)) :
    Topology.P1 (closure (⋃ i, S i : Set X)) := by
  -- First, `P1` holds for the union `⋃ i, S i`.
  have hUnion : Topology.P1 (⋃ i, S i : Set X) :=
    Topology.P1_iUnion_of_P1 (S := S) hS
  -- Then, apply the closure-stability of `P1`.
  exact Topology.P1_closure_of_P1 (A := ⋃ i, S i) hUnion
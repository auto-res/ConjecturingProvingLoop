

theorem Topology.frontier_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `hx.1` witnesses that `x` lies in the closure of `A ∩ B`.
  have h := (Topology.closure_inter_subset_inter_closure
      (A := A) (B := B)) hx.1
  exact h
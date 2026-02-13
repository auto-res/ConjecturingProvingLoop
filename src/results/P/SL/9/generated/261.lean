

theorem Topology.frontier_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `hx` gives that `x` is in the closure of `A ∩ B`.
  have h_cl : x ∈ closure (A ∩ B : Set X) := hx.1
  -- The closure of an intersection is contained in the intersection
  -- of the closures.
  have h_subset : closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  -- Combining the two facts yields the desired membership.
  exact h_subset h_cl
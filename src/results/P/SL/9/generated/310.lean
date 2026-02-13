

theorem Topology.frontier_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ closure A ∪ closure B := by
  intro x hx
  -- From `hx`, obtain membership in the closure of `A ∪ B`.
  have hx_closure : x ∈ closure (A ∪ B : Set X) := hx.1
  -- Rewrite the closure of the union using an existing lemma.
  have h_union : closure (A ∪ B : Set X) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Use the equality to convert membership.
  simpa [h_union] using hx_closure
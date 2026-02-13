

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier A ⊆ closure B := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hxClA : x ∈ closure A := hx.1
  -- Monotonicity of `closure` under the inclusion `A ⊆ B`.
  have hIncl : closure A ⊆ closure B := closure_mono hAB
  exact hIncl hxClA
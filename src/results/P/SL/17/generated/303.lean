

theorem Topology.frontier_subset_closure_interior_of_subset_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    frontier A ⊆ closure (interior (closure B)) := by
  intro x hx
  -- `x` lies in the closure of `A`.
  have hx_clA : x ∈ closure A := hx.1
  -- By monotonicity of `closure`, it also lies in the closure of `B`.
  have hx_clB : x ∈ closure B := (closure_mono hAB) hx_clA
  -- `P3 B` gives `B ⊆ interior (closure B)`, hence
  -- `closure B ⊆ closure (interior (closure B))`.
  have h_subset : closure B ⊆ closure (interior (closure B)) :=
    closure_mono (hP3B : B ⊆ interior (closure B))
  exact h_subset hx_clB
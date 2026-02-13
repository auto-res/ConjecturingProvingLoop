

theorem Topology.frontier_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior A)) ⊆ frontier A := by
  intro x hx
  -- `hx.1` gives `x ∈ closure (closure (interior A))`; simplify the double closure.
  have hClCI : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx.1
  -- Monotonicity of `closure` under `interior A ⊆ A`.
  have hClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hClCI
  -- Show that `x ∉ interior A`; otherwise we contradict `hx.2`.
  have hNotIntA : x ∉ interior A := by
    intro hIntA
    have hSubset :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have : x ∈ interior (closure (interior A)) := hSubset hIntA
    exact hx.2 this
  exact And.intro hClA hNotIntA


theorem Topology.frontier_subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    frontier (A : Set X) ⊆ closure (interior A) := by
  intro x hx
  -- `hx` gives `x ∈ closure A`.
  have hx_closureA : x ∈ closure (A : Set X) := hx.1
  -- From `P1`, obtain `closure A ⊆ closure (interior A)`.
  have h_subset : closure (A : Set X) ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono hA
  -- Conclude the desired membership.
  exact h_subset hx_closureA


theorem Topology.boundary_subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    closure (A : Set X) \ interior A ⊆ closure (interior A) := by
  intro x hx
  -- `hx` provides `x ∈ closure A`.
  have hx_closureA : x ∈ closure A := hx.1
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have h_closure_subset : closure A ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := hP1
    have h_closure : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hA_subset
    simpa [closure_closure] using h_closure
  -- Therefore, `x ∈ closure (interior A)`.
  exact h_closure_subset hx_closureA
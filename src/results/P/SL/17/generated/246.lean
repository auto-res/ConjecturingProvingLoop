

theorem Topology.frontier_subset_closure_interior_of_subset_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    frontier A ⊆ closure (interior B) := by
  intro x hx
  -- From `x ∈ frontier A`, obtain `x ∈ closure A`.
  have hx_clA : x ∈ closure A := hx.1
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_cl_subset : closure A ⊆ closure B := closure_mono hAB
  have hx_clB : x ∈ closure B := h_cl_subset hx_clA
  -- `P1 B` gives `B ⊆ closure (interior B)`.
  have hB_subset : B ⊆ closure (interior B) := hP1B
  -- Taking closures preserves inclusions; simplify `closure (closure _)`.
  have h_clB_subset : closure B ⊆ closure (interior B) := by
    simpa [closure_closure] using closure_mono hB_subset
  -- Combine the inclusions to conclude the desired membership.
  exact h_clB_subset hx_clB
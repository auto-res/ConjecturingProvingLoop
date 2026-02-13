

theorem Topology.boundary_subset_closure_inter_closureCompl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  -- `x` lies in `closure A`.
  have hx_closureA : x ∈ closure A := hx.1
  -- By a previously proven lemma, `x` also lies in `closure (Aᶜ)`.
  have hx_closureAc : x ∈ closure (Aᶜ) :=
    (Topology.boundary_subset_closure_compl (A := A)) hx
  -- Combine the two facts.
  exact ⟨hx_closureA, hx_closureAc⟩
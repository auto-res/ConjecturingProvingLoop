

theorem Topology.closure_inter_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A ∩ closure (interior A) : Set X) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    -- `closure (interior A)` is contained in `closure A`
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have hx_closureA : x ∈ closure A := h_subset hx
    exact And.intro hx_closureA hx


theorem Topology.boundary_subset_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure (Aᶜ : Set X) := by
  intro x hx
  -- `hx` provides that `x ∈ closure A` and `x ∉ interior A`.
  have h_not_int : (x : X) ∉ interior (A : Set X) := hx.2
  -- Since `closure (Aᶜ) = (interior A)ᶜ`, the non-membership just obtained
  -- translates into membership of `x` in `closure (Aᶜ)`.
  have h_eq := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have : (x : X) ∈ (interior (A : Set X))ᶜ := by
    simpa using h_not_int
  simpa [h_eq] using this
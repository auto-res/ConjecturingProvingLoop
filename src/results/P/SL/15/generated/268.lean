

theorem dense_iff_closure_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ ∀ x : X, closure A ∈ 𝓝 x := by
  constructor
  · intro hDense x
    -- Since `A` is dense, its closure is the whole space.
    have h_cl : (closure A : Set X) = Set.univ := hDense.closure_eq
    -- `univ` is a neighbourhood of every point.
    have h_nhds_univ : (Set.univ : Set X) ∈ 𝓝 x := by
      exact (isOpen_univ.mem_nhds trivial)
    simpa [h_cl] using h_nhds_univ
  · intro h
    -- Show that `closure A = univ`, whence density of `A`.
    have h_sub : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have h_nhds : closure A ∈ 𝓝 x := h x
      have h_int : x ∈ interior (closure A) :=
        (mem_interior_iff_mem_nhds).2 h_nhds
      exact interior_subset h_int
    have h_closure_eq : (closure A : Set X) = Set.univ := by
      apply Set.Subset.antisymm
      · intro x _; trivial
      · exact h_sub
    exact ((dense_iff_closure_eq (s := A)).2 h_closure_eq)


theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x` lies in `interior A`
      have h_open : IsOpen (interior A) := isOpen_interior
      have h_nhds : interior A ∈ 𝓝 x := h_open.mem_nhds hA
      have h_sub : interior A ⊆ A ∪ B := by
        intro y hy
        exact Or.inl (interior_subset hy)
      have h_union : A ∪ B ∈ 𝓝 x := Filter.mem_of_superset h_nhds h_sub
      exact (mem_interior_iff_mem_nhds).2 h_union
  | inr hB =>
      -- `x` lies in `interior B`
      have h_open : IsOpen (interior B) := isOpen_interior
      have h_nhds : interior B ∈ 𝓝 x := h_open.mem_nhds hB
      have h_sub : interior B ⊆ A ∪ B := by
        intro y hy
        exact Or.inr (interior_subset hy)
      have h_union : A ∪ B ∈ 𝓝 x := Filter.mem_of_superset h_nhds h_sub
      exact (mem_interior_iff_mem_nhds).2 h_union
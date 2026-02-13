

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- `x` is in the interior of `A`, hence every neighbourhood of `x` meets `interior A`
  have h_int_nhds : (interior A : Set X) ∈ 𝓝 x :=
    isOpen_interior.mem_nhds hx
  -- Since `interior A ⊆ closure (interior A)`, the latter is also in the neighbourhood filter
  have h_cl_nhds : (closure (interior A) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_int_nhds
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Re-express the set using `interior_interior` so that types match the goal
  have h_cl_nhds' : (closure (interior (interior A)) : Set X) ∈ 𝓝 x := by
    simpa [interior_interior] using h_cl_nhds
  -- Conclude that `x` belongs to the required interior
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds'
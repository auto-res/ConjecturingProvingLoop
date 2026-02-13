

theorem P2_basis {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U ∈ 𝓝 x, U ⊆ A) → P2 A := by
  intro hBasis
  intro x hxA
  -- Obtain a neighbourhood of `x` contained in `A`.
  rcases hBasis x hxA with ⟨U, hU_nhds, hU_sub⟩
  -- Therefore `A` itself is a neighbourhood of `x`.
  have hA_nhds : (A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset hU_nhds hU_sub
  -- Hence `x` lies in the interior of `A`.
  have hx_intA : x ∈ interior A :=
    (mem_interior_iff_mem_nhds).2 hA_nhds
  -- `interior A` is open and contained in `closure (interior A)`,
  -- so it is contained in the interior of that closure.
  have hsubset :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact hsubset hx_intA

theorem P1_basis {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ A) → P1 A := by
  intro hBasis
  intro x hxA
  rcases hBasis x hxA with ⟨U, hUopen, hxU, hUsub⟩
  have hA_nhds : (A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset (hUopen.mem_nhds hxU) hUsub
  have hx_int : x ∈ interior A := (mem_interior_iff_mem_nhds).2 hA_nhds
  exact subset_closure hx_int
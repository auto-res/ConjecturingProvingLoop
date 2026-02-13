

theorem P3_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (e '' A) := by
  classical
  -- The homeomorphism transports `interior (closure A)` as expected.
  have hImage :
      (e '' interior (closure A) : Set Y) =
        interior (closure (e '' A)) := by
    calc
      e '' interior (closure A)
          = interior (e '' closure A) := by
            simpa using e.image_interior (s := closure A)
      _ = interior (closure (e '' A)) := by
            simpa [e.image_closure (s := A)]
  ------------------------------------------------------------------
  -- Forward direction: `P3 A → P3 (e '' A)`.
  ------------------------------------------------------------------
  have forward : P3 A → P3 (e '' A) := by
    intro hP3
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure A) := hP3 hxA
    have : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
    simpa [hImage] using this
  ------------------------------------------------------------------
  -- Backward direction: `P3 (e '' A) → P3 A`.
  ------------------------------------------------------------------
  have backward : P3 (e '' A) → P3 A := by
    intro hP3img
    intro x hxA
    have h1 : e x ∈ interior (closure (e '' A)) :=
      hP3img ⟨x, hxA, rfl⟩
    have h2 : e x ∈ e '' interior (closure A) := by
      simpa [hImage] using h1
    rcases h2 with ⟨x', hx'int, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'int
  ------------------------------------------------------------------
  -- Assemble the equivalence.
  ------------------------------------------------------------------
  exact ⟨forward, backward⟩

theorem P1_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (e '' A) := by
  classical
  -- Auxiliary equality transporting `closure (interior A)` through the homeomorphism.
  have hImage :
      (e '' closure (interior A) : Set Y) =
        closure (interior (e '' A)) := by
    calc
      (e '' closure (interior A) : Set Y)
          = closure (e '' interior A) := by
              simpa using e.image_closure (s := interior A)
      _     = closure (interior (e '' A)) := by
        have hInt : (e '' interior A : Set Y) = interior (e '' A) := by
          simpa using e.image_interior (s := A)
        simpa [hInt]
  ------------------------------------------------------------------
  -- Forward direction: `P1 A → P1 (e '' A)`.
  ------------------------------------------------------------------
  have forward : P1 A → P1 (e '' A) := by
    intro hP1
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    have h_mem : e x ∈ (e '' closure (interior A) : Set Y) := ⟨x, hx_cl, rfl⟩
    simpa [hImage] using h_mem
  ------------------------------------------------------------------
  -- Backward direction: `P1 (e '' A) → P1 A`.
  ------------------------------------------------------------------
  have backward : P1 (e '' A) → P1 A := by
    intro hP1img
    intro x hxA
    have h1 : e x ∈ closure (interior (e '' A)) :=
      hP1img ⟨x, hxA, rfl⟩
    have h2 : e x ∈ (e '' closure (interior A) : Set Y) := by
      simpa [hImage] using h1
    rcases h2 with ⟨x', hx'cl, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'cl
  ------------------------------------------------------------------
  -- Assemble the equivalence.
  ------------------------------------------------------------------
  exact ⟨forward, backward⟩

theorem P2_basis_open {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ A) → P2 A := by
  intro hBasis
  intro x hxA
  -- Obtain an open neighbourhood whose closure stays inside `A`.
  rcases hBasis x hxA with ⟨U, hUopen, hxU, hUclosure⟩
  ------------------------------------------------------------------
  -- 1.  `U ⊆ A`.
  ------------------------------------------------------------------
  have hU_sub_A : (U : Set X) ⊆ A := by
    intro y hyU
    have : (y : X) ∈ closure U := subset_closure hyU
    exact hUclosure this
  ------------------------------------------------------------------
  -- 2.  `U ⊆ interior A`, hence `x ∈ interior A`.
  ------------------------------------------------------------------
  have hU_sub_intA : (U : Set X) ⊆ interior A := by
    intro y hyU
    have hA_nhds : (A : Set X) ∈ 𝓝 y :=
      Filter.mem_of_superset (hUopen.mem_nhds hyU) hU_sub_A
    exact (mem_interior_iff_mem_nhds).2 hA_nhds
  have hx_intA : x ∈ interior A := hU_sub_intA hxU
  ------------------------------------------------------------------
  -- 3.  `interior A ⊆ interior (closure (interior A))`.
  ------------------------------------------------------------------
  have hsubset :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  ------------------------------------------------------------------
  -- 4.  Conclude the desired membership.
  ------------------------------------------------------------------
  exact hsubset hx_intA
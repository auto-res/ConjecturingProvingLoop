

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    simpa [hA.interior_eq] using this
  have hx' : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact (interior_mono h_subset) hx'

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hx' : (x : X) ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx'

theorem P3_of_P2 {A : Set X} (h : P2 A) : P3 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : (closure (interior A) : Set X) ⊆ closure A := by
    have : (interior A : Set X) ⊆ A := interior_subset
    exact closure_mono this
  exact (interior_mono hsubset) hx'

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x ∈ A`
      have hxA : x ∈ closure (interior A) := hA hAx
      -- `interior A ⊆ interior (A ∪ B)`
      have hsubset : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono this
      -- therefore `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have hxAB : x ∈ closure (interior (A ∪ B)) :=
        (closure_mono hsubset) hxA
      exact hxAB
  | inr hBx =>
      -- `x ∈ B`
      have hxB : x ∈ closure (interior B) := hB hBx
      -- `interior B ⊆ interior (A ∪ B)`
      have hsubset : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono this
      -- therefore `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hxAB : x ∈ closure (interior (A ∪ B)) :=
        (closure_mono hsubset) hxB
      exact hxAB

theorem P3_diff {A B : Set X} (hA : P3 A) (hB : IsClosed B) : P3 (A \ B) := by
  intro x hx
  -- `hx` : `x ∈ A \ B`
  -- from `P3 A` we know that `x ∈ interior (closure A)`
  have hxAint : x ∈ interior (closure A) := hA hx.1
  -- define `U := interior (closure A) ∩ Bᶜ`
  set U : Set X := interior (closure A) ∩ (Bᶜ) with hUdef
  -- `U` is open
  have hUopen : IsOpen U := by
    have h1 : IsOpen (interior (closure A)) := isOpen_interior
    have h2 : IsOpen (Bᶜ) := hB.isOpen_compl
    simpa [hUdef] using h1.inter h2
  -- `x` belongs to `U`
  have hxU : x ∈ U := by
    have : x ∈ interior (closure A) ∧ x ∈ Bᶜ :=
      ⟨hxAint, (by
        -- `x ∉ B` because `x ∈ A \ B`
        simpa using hx.2)⟩
    simpa [hUdef] using this
  -- we show that `U ⊆ closure (A \ B)`
  have hUsubset : (U : Set X) ⊆ closure (A \ B) := by
    intro y hyU
    -- we prove `y ∈ closure (A \ B)` using the neighbourhood formulation
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- consider the open set `W = V ∩ U`
      have hWopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hyW : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- `y` lies in `closure A`
      have hyUdecomp : y ∈ interior (closure A) ∧ y ∈ Bᶜ := by
        simpa [hUdef] using hyU
      have hy_clA : y ∈ closure A := interior_subset hyUdecomp.1
      -- hence `W` meets `A`
      have h_nonempty : ((V ∩ U) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ U) hWopen hyW
      rcases h_nonempty with ⟨z, hz⟩
      -- `hz` gives the witness `z`
      have hzV : z ∈ V := hz.1.1
      have hzU : z ∈ U := hz.1.2
      have hzA : z ∈ A := hz.2
      -- from `z ∈ U` we get `z ∉ B`
      have hz_notB : z ∉ B := by
        have hzUdecomp : z ∈ interior (closure A) ∧ z ∈ Bᶜ := by
          simpa [hUdef] using hzU
        simpa using hzUdecomp.2
      -- assemble the witness for `V ∩ (A \ B)`
      exact ⟨z, ⟨hzV, ⟨hzA, hz_notB⟩⟩⟩
    exact this
  -- `U` is an open neighbourhood of `x` contained in `closure (A \ B)`
  have h_nhds : (closure (A \ B) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset (hUopen.mem_nhds hxU) hUsubset
  -- therefore `x ∈ interior (closure (A \ B))`
  exact (mem_interior_iff_mem_nhds).2 h_nhds
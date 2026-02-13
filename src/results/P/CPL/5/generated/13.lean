

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Embedding f) {A : Set X} : P3 (f '' A) → P3 A := by
  classical
  intro hP3
  intro x hxA
  -- `f x` lies in the interior of the closure of the image of `A`
  have hfx_int : f x ∈ interior (closure (f '' A)) := by
    have : f x ∈ (f '' A) := ⟨x, hxA, rfl⟩
    exact hP3 this
  -- Let `U` be the preimage of that interior
  let U : Set X := f ⁻¹' interior (closure (f '' A))
  have hU_open : IsOpen U := by
    have : IsOpen (interior (closure (f '' A))) := isOpen_interior
    simpa [U] using this.preimage hf.continuous
  have hxU : x ∈ U := by
    have : f x ∈ interior (closure (f '' A)) := hfx_int
    simpa [U, Set.mem_preimage] using this
  -- Show: `U ⊆ closure A`
  have hU_subset : (U : Set X) ⊆ closure (A : Set X) := by
    intro y hyU
    -- `f y` is in the interior, hence in the closure
    have hy_int : f y ∈ interior (closure (f '' A)) := by
      simpa [U, Set.mem_preimage] using hyU
    have hy_cl : f y ∈ closure (f '' A) := interior_subset hy_int
    -- If already in the closure we're done
    by_cases h_clA : y ∈ closure (A : Set X)
    · exact h_clA
    -- Otherwise derive a contradiction
    · have hOpenCompl : IsOpen ((closure (A : Set X))ᶜ) :=
        isClosed_closure.isOpen_compl
      -- Obtain an open set `V` in `Y` whose preimage is this complement
      rcases (hf.inducing.isOpen_iff).1 hOpenCompl with ⟨V, hVopen, hVpre⟩
      -- `y` is in the complement, so `f y ∈ V`
      have hyV : f y ∈ V := by
        have hyCompl : y ∈ ((closure (A : Set X))ᶜ) := by
          simpa using h_clA
        have : y ∈ f ⁻¹' V := by
          simpa [hVpre] using hyCompl
        simpa [Set.mem_preimage] using this
      -- Show that `V` is disjoint from `f '' A`
      have h_disjoint : V ∩ f '' A = (∅ : Set Y) := by
        apply Set.eq_empty_iff_forall_not_mem.2
        intro w hw
        rcases hw.2 with ⟨z, hzA, rfl⟩
        have hz_pre : z ∈ f ⁻¹' V := by
          change f z ∈ V
          exact hw.1
        have hz_not_cl : z ∈ ((closure (A : Set X))ᶜ) := by
          simpa [hVpre] using hz_pre
        have hz_cl : z ∈ closure (A : Set X) := subset_closure hzA
        exact (hz_not_cl hz_cl).elim
      -- But `f y` is in the closure of `f '' A`, so every neighborhood meets it
      have h_ne : (V ∩ f '' A).Nonempty :=
        (mem_closure_iff).1 hy_cl V hVopen hyV
      simpa [h_disjoint] using h_ne
  -- `U` is an open neighborhood of `x` contained in `closure A`
  have hU_to_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_maximal hU_subset hU_open
  have : x ∈ interior (closure (A : Set X)) := hU_to_int hxU
  exact this
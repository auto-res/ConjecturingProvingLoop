

theorem P2_finite_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) h)

theorem P2_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) {A : Set X} : P2 (f '' A) → P2 A := by
  classical
  intro hP2
  intro x hxA
  -- Image point satisfies the `P2` condition.
  have hfx :
      f x ∈ interior (closure (interior (f '' A))) :=
    hP2 ⟨x, hxA, rfl⟩
  -- An auxiliary open neighbourhood on the source.
  set U : Set X := f ⁻¹' interior (closure (interior (f '' A))) with hUdef
  have hU_open : IsOpen U := by
    have : IsOpen (interior (closure (interior (f '' A)))) :=
      isOpen_interior
    simpa [hUdef] using this.preimage hf.continuous
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfx
  ----------------------------------------------------------------
  -- Main inclusion: `U ⊆ closure (interior A)`.
  ----------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro y hyU
    -- Image of `y` lies in the closure.
    have hfy_cl :
        f y ∈ closure (interior (f '' A)) := by
      have : f y ∈ interior (closure (interior (f '' A))) := by
        simpa [hUdef, Set.mem_preimage] using hyU
      exact interior_subset this
    -- If `y` is already in the desired closure we are done.
    by_cases hmem : y ∈ closure (interior A)
    · exact hmem
    -- Otherwise derive a contradiction.
    have hCopen : IsOpen ((closure (interior A))ᶜ) :=
      isClosed_closure.isOpen_compl
    have hyC : y ∈ (closure (interior A))ᶜ := hmem
    -- Transport openness via the embedding.
    obtain ⟨V, hVopen, hVpre⟩ :=
      (hf.inducing.isOpen_iff).1 hCopen
    have hyV : f y ∈ V := by
      have : y ∈ f ⁻¹' V := by
        simpa [hVpre] using hyC
      simpa [Set.mem_preimage] using this
    ----------------------------------------------------------------
    -- Show `V` is disjoint from `interior (f '' A)`.
    ----------------------------------------------------------------
    have hV_disj : V ∩ interior (f '' A) = (∅ : Set Y) := by
      apply Set.eq_empty_iff_forall_not_mem.2
      intro w hw
      rcases hw with ⟨hwV, hwInt⟩
      -- Lift `w` to the source.
      have hwImg : w ∈ f '' A := interior_subset hwInt
      rcases hwImg with ⟨z, hzA, hw_eq⟩
      -- Obtain an open nbhd witnessing `w ∈ interior (f '' A)`.
      rcases(mem_interior.1 hwInt) with ⟨W, hWsub, hWopen, hwW⟩
      -- Pull back this nbhd.
      let H : Set X := f ⁻¹' W
      have hHopen : IsOpen H :=
        hWopen.preimage hf.continuous
      have hHsub : (H : Set X) ⊆ A := by
        intro t htH
        have hf_t_W : f t ∈ W := htH
        have hf_t_img : f t ∈ f '' A := hWsub hf_t_W
        rcases hf_t_img with ⟨a', ha'A, h_eq'⟩
        have ht_eq : t = a' := by
          apply hf.injective
          exact h_eq'.symm
        simpa [ht_eq] using ha'A
      have hzH : z ∈ H := by
        change f z ∈ W
        simpa [hw_eq] using hwW
      -- Hence `z ∈ interior A`.
      have hz_intA : z ∈ interior A :=
        mem_interior.2 ⟨H, hHsub, hHopen, hzH⟩
      -- And thus `z ∈ closure (interior A)`.
      have hz_cl : z ∈ closure (interior A) :=
        subset_closure hz_intA
      -- Yet `f z = w ∈ V`, so `z` is also in the preimage of `V`.
      have hz_pre : z ∈ f ⁻¹' V := by
        change f z ∈ V
        simpa [hw_eq] using hwV
      have hz_not : z ∈ (closure (interior A))ᶜ := by
        simpa [hVpre] using hz_pre
      exact (hz_not hz_cl).elim
    ----------------------------------------------------------------
    -- But `f y` is in the closure of that interior — contradiction.
    ----------------------------------------------------------------
    have hNon : (V ∩ interior (f '' A)).Nonempty :=
      (mem_closure_iff).1 hfy_cl V hVopen hyV
    simpa [hV_disj] using hNon
  ----------------------------------------------------------------
  -- Maximality of the interior gives the desired membership for `x`.
  ----------------------------------------------------------------
  have hx_int :
      x ∈ interior (closure (interior A)) :=
    (interior_maximal hU_subset hU_open) hxU
  exact hx_int

theorem P1_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) {A : Set X} : P1 (f '' A) → P1 A := by
  intro hP1
  intro x hxA
  classical
  -- `f x` is in the closure of the interior of the image.
  have hfx_cl : f x ∈ closure (interior (f '' A)) :=
    hP1 ⟨x, hxA, rfl⟩
  -- We show that `x` is in the closure of the interior of `A`.
  have : x ∈ closure (interior A) := by
    -- Use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- Find an open set `W` in `Y` whose preimage is `V`.
    obtain ⟨W, hWopen, hWpre⟩ :=
      (hf.inducing.isOpen_iff).1 hVopen
    -- `f x` belongs to `W`.
    have hxW : f x ∈ W := by
      have : x ∈ (f ⁻¹' W) := by
        simpa [hWpre] using hxV
      simpa [Set.mem_preimage] using this
    -- `W` meets `interior (f '' A)`.
    have h_non : (W ∩ interior (f '' A)).Nonempty :=
      (mem_closure_iff).1 hfx_cl W hWopen hxW
    rcases h_non with ⟨y, hyW, hyInt⟩
    -- Write `y` as `f z` with `z ∈ A`.
    have hyImg : y ∈ f '' A := interior_subset hyInt
    rcases hyImg with ⟨z, hzA, rfl⟩
    -- Show `z ∈ V`.
    have hzV : z ∈ V := by
      have : f z ∈ W := hyW
      have : z ∈ f ⁻¹' W := by
        simpa [Set.mem_preimage] using this
      simpa [hWpre] using this
    -- Show `z ∈ interior A`.
    have hzIntA : z ∈ interior A := by
      -- From `f z ∈ interior (f '' A)` obtain a suitable open neighbourhood.
      rcases mem_interior.1 hyInt with ⟨U', hU'sub, hU'open, hzyU'⟩
      -- Pull it back to `X`.
      let H : Set X := f ⁻¹' U'
      have hHopen : IsOpen H := hU'open.preimage hf.continuous
      have hzH : z ∈ H := by
        dsimp [H]; simpa using hzyU'
      -- `H` is contained in `A`.
      have hHsubA : (H : Set X) ⊆ A := by
        intro t htH
        have hftU' : f t ∈ U' := htH
        have hftImg : f t ∈ f '' A := hU'sub hftU'
        rcases hftImg with ⟨w, hwA, hw_eq⟩
        have ht_eq : t = w := by
          apply hf.injective
          exact hw_eq.symm
        simpa [ht_eq] using hwA
      exact
        mem_interior.2 ⟨H, hHsubA, hHopen, hzH⟩
    -- Provide the required witness in `V ∩ interior A`.
    exact ⟨z, hzV, hzIntA⟩
  exact this

theorem P1_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  exact (P1_iff_dense_interior (A := A)).1 hP1

theorem P3_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → interior (closure A) = interior (closure (closure A)) := by
  intro _
  simp [closure_closure]
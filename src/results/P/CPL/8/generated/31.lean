

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A → P1 (f '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` comes from `A`
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Use the neighborhood characterization of the closure
  refine (mem_closure_iff).2 ?_
  intro V hVopen hfxV
  -- Pull the neighbourhood `V` back through `f`
  have hUopen : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
  have hxU : x ∈ f ⁻¹' V := by
    simpa [Set.mem_preimage] using hfxV
  -- Since `x` is in the closure of `interior A`, the pull-back meets `interior A`
  have h_nonempty : ((f ⁻¹' V) ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hx_cl (f ⁻¹' V) hUopen hxU
    simpa using this
  rcases h_nonempty with ⟨z, hzU, hzIntA⟩
  have hzV : f z ∈ V := by
    simpa [Set.mem_preimage] using hzU
  -- Show that `f z` lies in `interior (f '' A)`
  have hzIntFA : f z ∈ interior (f '' A) := by
    -- `f '' interior A` is an open subset of `f '' A`
    have h_open_fint : IsOpen (f '' interior A) := by
      have hf : IsOpenMap f := f.isOpenMap
      simpa using hf (interior A) isOpen_interior
    have h_sub_fint : (f '' interior A : Set _) ⊆ f '' A := by
      intro w hw
      rcases hw with ⟨u, huInt, rfl⟩
      exact ⟨u, interior_subset huInt, rfl⟩
    have h_subset : (f '' interior A : Set _) ⊆ interior (f '' A) :=
      interior_maximal h_sub_fint h_open_fint
    have hfz_mem : f z ∈ f '' interior A := ⟨z, hzIntA, rfl⟩
    exact h_subset hfz_mem
  exact ⟨f z, ⟨hzV, hzIntFA⟩⟩

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (f ⁻¹' B) := by
  intro hP2B
  intro x hx
  -- `hx` gives `f x ∈ B`.
  have hfxB : f x ∈ B := by
    simpa [Set.mem_preimage] using hx
  -- Apply `P2 B`.
  have hfx : f x ∈ interior (closure (interior B)) := hP2B hfxB
  -- Auxiliary open sets in `Y` and their preimages in `X`.
  set V : Set Y := interior (closure (interior B)) with hVdef
  have hVopen : IsOpen V := by
    simpa [hVdef] using isOpen_interior
  have hfxV : f x ∈ V := by
    simpa [hVdef] using hfx
  set U : Set X := f ⁻¹' V with hUdef
  have hUopen : IsOpen U := by
    have : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
    simpa [hUdef] using this
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfxV
  -- Show that every point of `U` lies in `closure (interior (f ⁻¹' B))`.
  have hU_sub : (U : Set X) ⊆ closure (interior (f ⁻¹' B)) := by
    intro y hyU
    -- `f y` lies in `V`.
    have hfyV : f y ∈ V := by
      simpa [hUdef, Set.mem_preimage] using hyU
    -- Hence `f y ∈ closure (interior B)`.
    have hfy_cl : f y ∈ closure (interior B) := by
      have hVsubset : (V : Set Y) ⊆ closure (interior B) := by
        intro z hz
        exact interior_subset hz
      exact hVsubset hfyV
    -- Prove `y ∈ closure (interior (f ⁻¹' B))`.
    have : y ∈ closure (interior (f ⁻¹' B)) := by
      -- Neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- Open set in `Y` obtained via `f.symm`.
      set T : Set Y := f.symm ⁻¹' W with hTdef
      have hTopen : IsOpen T := by
        have : IsOpen (f.symm ⁻¹' W) := hWopen.preimage f.symm.continuous
        simpa [hTdef] using this
      -- `f y` belongs to `T`.
      have hfyT : f y ∈ T := by
        have : y ∈ W := hyW
        simpa [hTdef, Set.mem_preimage, f.symm_apply_apply] using this
      -- Intersect with `interior B`.
      have hNonempty : (T ∩ interior B).Nonempty :=
        (mem_closure_iff).1 hfy_cl T hTopen hfyT
      rcases hNonempty with ⟨z, hzT, hzInt⟩
      -- Pull the point back to `X`.
      have hwW : f.symm z ∈ W := by
        have : z ∈ T := hzT
        simpa [hTdef, Set.mem_preimage] using this
      have hwInt : f.symm z ∈ interior (f ⁻¹' B) := by
        -- First, membership in `f ⁻¹' interior B`.
        have hw_pre : f.symm z ∈ f ⁻¹' interior B := by
          have : f (f.symm z) ∈ interior B := by
            simpa [f.apply_symm_apply] using hzInt
          simpa [Set.mem_preimage] using this
        -- Upgrade to the interior using maximality.
        have hOpenPre : IsOpen (f ⁻¹' interior B) :=
          (isOpen_interior).preimage f.continuous
        have hSub : (f ⁻¹' interior B : Set X) ⊆ f ⁻¹' B := by
          intro t ht
          simpa [Set.mem_preimage] using interior_subset ht
        have hSubset :
            (f ⁻¹' interior B : Set X) ⊆ interior (f ⁻¹' B) :=
          interior_maximal hSub hOpenPre
        exact hSubset hw_pre
      exact ⟨f.symm z, ⟨hwW, hwInt⟩⟩
    simpa using this
  -- Use the open neighbourhood `U` to finish.
  have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
  have h_mem : x ∈ interior (closure (interior (f ⁻¹' B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hU_sub)
  simpa using h_mem


theorem interior_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → interior A ⊆ interior (closure A) := by
  intro _hP3
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x ∈ A`, obtain the auxiliary membership from `P2`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- An auxiliary open neighbourhood of `x`.
  let U : Set X := interior (closure (interior A))
  have hUx : x ∈ U := by
    simpa [U] using hxInt
  have hUopen : IsOpen U := by
    have : IsOpen (interior (closure (interior A))) := isOpen_interior
    simpa [U] using this
  have hUsubset : (U : Set X) ⊆ closure (interior A) := by
    have : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    simpa [U] using this
  -- Image of `U` through `f`.
  let V : Set Y := f '' U
  have hVopen : IsOpen V := by
    have hf : IsOpenMap f := f.isOpenMap
    have : IsOpen (f '' U) := hf _ hUopen
    simpa [V] using this
  have hyV : f x ∈ V := by
    dsimp [V]; exact ⟨x, hUx, rfl⟩
  -- Show that `V` is contained in the required closure.
  have hVsub : (V : Set Y) ⊆ closure (interior (f '' A)) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `w ∈ closure (interior A)`
    have hwCl : w ∈ closure (interior A) := hUsubset hwU
    -- Show `f w ∈ closure (interior (f '' A))`.
    have : f w ∈ closure (interior (f '' A)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hWopen hfwW
      -- Pull `W` back via `f`.
      have hPreOpen : IsOpen (f ⁻¹' W) := hWopen.preimage f.continuous
      have hwPre : w ∈ f ⁻¹' W := by
        simpa [Set.mem_preimage] using hfwW
      -- `w` is in the closure of `interior A`, hence the intersection is non-empty.
      have hNonempty :
          ((f ⁻¹' W) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hwCl (f ⁻¹' W) hPreOpen hwPre
      rcases hNonempty with ⟨u, huPre, huIntA⟩
      -- Map the witness back to `Y`.
      have hfuW : f u ∈ W := by
        have : u ∈ f ⁻¹' W := huPre
        simpa [Set.mem_preimage] using this
      -- `f u` lies in `interior (f '' A)`.
      have hfuInt : f u ∈ interior (f '' A) := by
        -- `f '' interior A` is open.
        have hOpen_fint : IsOpen (f '' interior A) := by
          have hf : IsOpenMap f := f.isOpenMap
          simpa using hf _ isOpen_interior
        -- Inclusion into `f '' A`.
        have hSub : (f '' interior A : Set Y) ⊆ f '' A := by
          intro v hv
          rcases hv with ⟨t, htInt, rfl⟩
          exact ⟨t, interior_subset htInt, rfl⟩
        have hSubInt :
            (f '' interior A : Set Y) ⊆ interior (f '' A) :=
          interior_maximal hSub hOpen_fint
        have : f u ∈ f '' interior A := ⟨u, huIntA, rfl⟩
        exact hSubInt this
      exact ⟨f u, ⟨hfuW, hfuInt⟩⟩
    exact this
  -- `V` is an open neighbourhood of `f x` contained in the desired set,
  -- hence `f x` belongs to the required interior.
  have hNhd : (V : Set Y) ∈ 𝓝 (f x) := hVopen.mem_nhds hyV
  have hNhd' :
      (closure (interior (f '' A)) : Set Y) ∈ 𝓝 (f x) :=
    Filter.mem_of_superset hNhd hVsub
  have h_mem :
      f x ∈ interior (closure (interior (f '' A))) :=
    (mem_interior_iff_mem_nhds).2 hNhd'
  simpa using h_mem

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (f ⁻¹' B) := by
  intro hP1B
  -- Transfer the property through the inverse homeomorphism.
  have hP1_pre : P1 ((f.symm) '' B) :=
    P1_image_homeomorph (f := f.symm) hP1B
  -- Identify the image with the preimage.
  have hEq : ((f.symm) '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyB, rfl⟩
      show f (f.symm y) ∈ B
      simpa using hyB
    · intro hx
      have hfxB : f x ∈ B := by
        simpa [Set.mem_preimage] using hx
      exact
        ⟨f x, hfxB, by
          simpa using (f.symm_apply_apply x)⟩
  -- Establish `P1` for the preimage.
  intro x hx
  have hx' : x ∈ ((f.symm) '' B) := by
    simpa [hEq] using hx
  have h_cl : x ∈ closure (interior ((f.symm) '' B)) := hP1_pre hx'
  simpa [hEq] using h_cl

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (f ⁻¹' B) := by
  intro hP3B
  intro x hx
  -- `hx` gives `f x ∈ B`.
  have hfxB : f x ∈ B := by
    simpa [Set.mem_preimage] using hx
  -- Apply `P3 B`.
  have hfxInt : f x ∈ interior (closure B) := hP3B hfxB
  -- Auxiliary open set in `Y`.
  set V : Set Y := interior (closure B) with hVdef
  have hVopen : IsOpen V := by
    simpa [hVdef] using isOpen_interior
  have hfxV : f x ∈ V := by
    simpa [hVdef] using hfxInt
  -- Pull the open set back to `X`.
  set U : Set X := f ⁻¹' V with hUdef
  have hUopen : IsOpen U := by
    have : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
    simpa [hUdef] using this
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfxV
  -- Show that every point of `U` lies in the closure of `f ⁻¹' B`.
  have hU_sub : (U : Set X) ⊆ closure (f ⁻¹' B) := by
    intro y hyU
    -- `f y` lies in `V ⊆ closure B`.
    have hfyV : f y ∈ V := by
      simpa [hUdef, Set.mem_preimage] using hyU
    have hfy_clB : f y ∈ closure B := by
      have hVsubset : (V : Set Y) ⊆ closure B := by
        intro z hz
        exact interior_subset hz
      exact hVsubset hfyV
    -- Prove that `y` belongs to the closure of `f ⁻¹' B`.
    have : y ∈ closure (f ⁻¹' B) := by
      -- Use the neighbourhood characterization of closure.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- The image of `W` under `f` is an open neighbourhood of `f y`.
      have hWimageOpen : IsOpen (f '' W) := by
        have hf : IsOpenMap f := f.isOpenMap
        simpa using hf W hWopen
      have hfyW : f y ∈ f '' W := by
        exact ⟨y, hyW, rfl⟩
      -- Because `f y` is in the closure of `B`, the intersection is nonempty.
      have hNonempty : ((f '' W) ∩ B).Nonempty :=
        (mem_closure_iff).1 hfy_clB _ hWimageOpen hfyW
      rcases hNonempty with ⟨z, hzFW, hzB⟩
      rcases hzFW with ⟨w, hwW, hw_eq⟩
      -- `w` witnesses the required intersection in `X`.
      have hwB : w ∈ f ⁻¹' B := by
        have : f w ∈ B := by
          simpa [hw_eq] using hzB
        simpa [Set.mem_preimage] using this
      exact ⟨w, hwW, hwB⟩
    exact this
  -- Use `U` to witness that `x` is in the interior of the closure.
  have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
  have hNhd' : (closure (f ⁻¹' B) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset hNhd hU_sub
  have h_mem : x ∈ interior (closure (f ⁻¹' B)) :=
    (mem_interior_iff_mem_nhds).2 hNhd'
  simpa using h_mem

theorem P2_of_P3_and_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P1 A → P2 A := by
  intro hP3 hP1 x hxA
  -- From `P1` we get the equality of the two closures.
  have h_closure_eq : closure (interior (A : Set X)) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  -- Apply `P3` to obtain membership in the interior of `closure A`.
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  -- Rewrite using the closure equality.
  simpa [h_closure_eq] using hx_int
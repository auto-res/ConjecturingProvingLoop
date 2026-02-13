

theorem P1_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 B → P1 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using P1_prod h_univ hB

theorem P2_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using P2_prod h_univ hB

theorem P3_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using P3_prod h_univ hB

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e ⁻¹' B) := by
  intro hB
  intro x hx
  -- `hx` gives that `e x ∈ B`.
  have hxB : (e x) ∈ B := hx
  -- Apply `P1` for `B`.
  have h_closure : (e x) ∈ closure (interior B) := hB hxB
  ----------------------------------------------------------------
  -- 1.  Transport the membership with `e.symm`.
  ----------------------------------------------------------------
  have h_in_image : x ∈ (⇑(e.symm)) '' closure (interior B) := by
    refine ⟨e x, h_closure, ?_⟩
    simp
  -- Rewrite the image of the closure.
  have h_image_cl :
      (⇑(e.symm)) '' closure (interior B) =
        closure ((⇑(e.symm)) '' interior B) := by
    simpa using e.symm.image_closure (s := interior B)
  have h_in_closure_image :
      x ∈ closure ((⇑(e.symm)) '' interior B) := by
    have : x ∈ (⇑(e.symm)) '' closure (interior B) := h_in_image
    simpa [h_image_cl] using this
  ----------------------------------------------------------------
  -- 2.  Relate the two interiors.
  ----------------------------------------------------------------
  -- First, identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_image_pre :
      (⇑(e.symm)) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa [e.apply_symm_apply] using hbB
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp
  -- Now rewrite the image of the interior.
  have h_image_int :
      (⇑(e.symm)) '' interior B = interior (e ⁻¹' B) := by
    have h := e.symm.image_interior (s := B)
    simpa [h_image_pre] using h
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  have : x ∈ closure (interior (e ⁻¹' B)) := by
    have : x ∈ closure ((⇑(e.symm)) '' interior B) := h_in_closure_image
    simpa [h_image_int] using this
  exact this

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (e ⁻¹' B) := by
  intro hB
  intro x hx
  -- `hx` tells us that `e x ∈ B`.
  have hxB : e x ∈ B := hx
  -- Apply `P2` for `B`.
  have h_mem : e x ∈ interior (closure (interior B)) := hB hxB
  ----------------------------------------------------------------
  -- 1.  Transport the membership with `e.symm`.
  ----------------------------------------------------------------
  have h_img :
      x ∈ (e.symm) '' interior (closure (interior B)) := by
    exact ⟨e x, h_mem, by
      simpa using (e.symm_apply_apply x)⟩
  -- Rewrite the image of an interior.
  have h_step1 :
      x ∈ interior ((e.symm) '' closure (interior B)) := by
    have h_eq :=
      e.symm.image_interior (s := closure (interior B))
    simpa [h_eq] using h_img
  -- Rewrite the image of a closure.
  have h_step2 :
      x ∈ interior (closure ((e.symm) '' interior B)) := by
    have h_eq := e.symm.image_closure (s := interior B)
    simpa [h_eq] using h_step1
  -- Rewrite the image of an interior once more.
  have h_step3 :
      x ∈ interior (closure (interior ((e.symm) '' B))) := by
    have h_eq := e.symm.image_interior (s := B)
    simpa [h_eq] using h_step2
  ----------------------------------------------------------------
  -- 2.  Identify `(e.symm) '' B` with the pre-image `e ⁻¹' B`.
  ----------------------------------------------------------------
  have h_image_pre : (e.symm) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa using hbB
    · intro hy
      exact ⟨e y, hy, by simp⟩
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [h_image_pre] using h_step3

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e ⁻¹' B) := by
  intro hB
  intro x hx
  have hxB : e x ∈ B := hx
  -- Step 1: use `hB`.
  have h_int : e x ∈ interior (closure B) := hB hxB
  -- Step 2: transport with `e.symm`.
  have h1 : x ∈ (e.symm) '' interior (closure B) := by
    refine ⟨e x, h_int, ?_⟩
    simp
  -- Rewrite the image of an interior.
  have h2 : x ∈ interior ((e.symm) '' closure B) := by
    simpa [e.symm.image_interior (s := closure B)] using h1
  -- Rewrite the image of a closure.
  have h3 : x ∈ interior (closure ((e.symm) '' B)) := by
    simpa [e.symm.image_closure (s := B)] using h2
  -- Identify the image with the preimage.
  have h_image_pre : (e.symm) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa using hbB
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp
  -- Conclude.
  simpa [h_image_pre] using h3
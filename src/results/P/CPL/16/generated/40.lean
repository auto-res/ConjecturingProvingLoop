

theorem P1_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∪ A) ↔ P1 A := by
  simpa [Set.union_self]

theorem P2_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (A ∪ A) ↔ P2 A := by
  simpa [Set.union_self]

theorem P3_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (A ∪ A) ↔ P3 A := by
  simpa [Set.union_self]

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P1 A → P1 (h '' A) := by
  intro hP1
  -- unpack the definition of `P1`
  unfold P1 at hP1 ⊢
  intro y hy
  -- pick a preimage point
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hP1 hxA
  -- first, put `h x` in `closure (h '' interior A)`
  have h_mem_small : (h x : Y) ∈ closure (h '' interior A) := by
    -- image of the closure under a homeomorphism
    have h_image_eq :
        (h '' closure (interior A) : Set Y) =
          closure (h '' interior A) := by
      simpa using h.image_closure (interior A)
    have : (h x : Y) ∈ h '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    simpa [h_image_eq] using this
  -- show that `h '' interior A ⊆ interior (h '' A)`
  have h_subset : (h '' interior A : Set Y) ⊆ interior (h '' A) := by
    -- the image of an open set by a homeomorphism is open
    have h_open_image_int : IsOpen (h '' interior A : Set Y) := by
      -- express it as the preimage of an open set by the continuous inverse
      have h_eq :
          (h '' interior A : Set Y) =
            {y : Y | h.symm y ∈ interior A} := by
        ext y
        constructor
        · rintro ⟨x, hxIntA, rfl⟩
          simpa using hxIntA
        · intro hy
          have hxIntA : h.symm y ∈ interior A := hy
          refine ⟨h.symm y, hxIntA, ?_⟩
          have : h (h.symm y) = y := h.apply_symm_apply y
          simpa [this]
      have h_preopen :
          IsOpen ((fun y : Y => h.symm y) ⁻¹' interior A) :=
        isOpen_interior.preimage h.symm.continuous
      simpa [Set.preimage, h_eq] using h_preopen
    -- and it is clearly contained in `h '' A`
    have h_sub : (h '' interior A : Set Y) ⊆ h '' A := by
      intro y hy
      rcases hy with ⟨x, hxIntA, rfl⟩
      exact ⟨x, interior_subset hxIntA, rfl⟩
    exact interior_maximal h_sub h_open_image_int
  -- use monotonicity of the closure
  have h_closure_mono :
      closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
    closure_mono h_subset
  exact h_closure_mono h_mem_small

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P2 A → P2 (h '' A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro y hy
  -- Pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the property coming from `P2 A`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
  -- Define the auxiliary open set `O`
  let O : Set Y := h '' interior (closure (interior A))
  -- `O` is open since `h` is a homeomorphism (hence an open map)
  have hO_open : IsOpen (O : Set Y) := by
    have h_open : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    simpa [O] using h.isOpenMap.image h_open
  -- We show that `O ⊆ closure (interior (h '' A))`
  have hO_sub : (O : Set Y) ⊆ closure (interior (h '' A)) := by
    -- First, show that `h '' interior A ⊆ interior (h '' A)`
    have h_img_int_subset :
        (h '' interior A : Set Y) ⊆ interior (h '' A) := by
      -- The image of an open set by a homeomorphism is open
      have h_open_img : IsOpen (h '' interior A : Set Y) := by
        have h_open_int : IsOpen (interior A : Set X) := isOpen_interior
        simpa using h.isOpenMap.image h_open_int
      -- And it is obviously contained in `h '' A`
      have h_sub : (h '' interior A : Set Y) ⊆ h '' A := by
        intro z hz
        rcases hz with ⟨x', hx'int, rfl⟩
        exact ⟨x', interior_subset hx'int, rfl⟩
      exact interior_maximal h_sub h_open_img
    -- Hence, by `closure_mono`,
    have h_closure_sub :
        closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
      closure_mono h_img_int_subset
    -- Finally, relate `O` to `closure (h '' interior A)`
    intro z hz
    dsimp [O] at hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- `h x'` is in `h '' closure (interior A)`
    have hz_in_closure :
        (h x' : Y) ∈ closure (h '' interior A) := by
      have : (h x' : Y) ∈ h '' closure (interior A) :=
        ⟨x', interior_subset hx'Int, rfl⟩
      simpa [h.image_closure (interior A)] using this
    exact h_closure_sub hz_in_closure
  -- Our point belongs to `O`
  have hxO : (h x : Y) ∈ O := by
    dsimp [O]
    exact ⟨x, hx_int, rfl⟩
  -- Since `O` is open and contained in the target set, we conclude
  have hIncl :
      (h x : Y) ∈ interior (closure (interior (h '' A))) :=
    (interior_maximal hO_sub hO_open) hxO
  exact hIncl

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {A : Set X} : P3 A → P3 (h '' A) := by
  intro hP3
  -- Unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro y hyImage
  -- Choose a preimage point `x` such that `h x = y`
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- From `P3 A` we know that `x ∈ interior (closure A)`
  have hxInt : (x : X) ∈ interior (closure A) := hP3 hxA
  -- Show that `h '' interior (closure A)` is contained in
  -- `interior (closure (h '' A))`
  have h_subset :
      (h '' interior (closure A) : Set Y) ⊆ interior (closure (h '' A)) := by
    -- The image of an open set by a homeomorphism is open
    have h_open :
        IsOpen (h '' interior (closure A) : Set Y) := by
      have h_open_src : IsOpen (interior (closure A) : Set X) :=
        isOpen_interior
      simpa using h.isOpenMap.image h_open_src
    -- And it is contained in the closure of `h '' A`
    have h_sub :
        (h '' interior (closure A) : Set Y) ⊆ closure (h '' A) := by
      intro z hz
      rcases hz with ⟨x', hx'int, rfl⟩
      -- `x'` lies in `interior (closure A)` so it lies in `closure A`
      have : (h x' : Y) ∈ h '' closure A := ⟨x', interior_subset hx'int, rfl⟩
      -- Use the lemma `image_closure` for a homeomorphism
      have h_eq : (h '' closure A : Set Y) = closure (h '' A) := by
        simpa using h.image_closure A
      simpa [h_eq] using this
    -- Conclude using `interior_maximal`
    exact interior_maximal h_sub h_open
  -- Our point `h x` belongs to `h '' interior (closure A)`
  have hxImage : (h x : Y) ∈ h '' interior (closure A) := ⟨x, hxInt, rfl⟩
  -- Therefore it belongs to the required interior
  exact h_subset hxImage

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → IsOpen A := by
  intro hClosed hP2
  -- `P2` gives the inclusion `A ⊆ interior (closure (interior A))`.
  have h₁ : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Since `A` is closed and `interior A ⊆ A`, we get
  -- `closure (interior A) ⊆ A`.
  have h_closure_subset : closure (interior A) ⊆ A := by
    have h : (interior A : Set X) ⊆ A := interior_subset
    -- `closure_minimal` upgrades this to an inclusion on closures.
    exact closure_minimal h hClosed
  -- By monotonicity of `interior`,
  have h₂ : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  -- Combining the two inclusions yields `A ⊆ interior A`.
  have hA_int : (A : Set X) ⊆ interior A := fun x hx => h₂ (h₁ hx)
  -- Together with the obvious `interior A ⊆ A`, we get equality.
  have h_eq : interior A = A :=
    Set.Subset.antisymm (interior_subset : interior A ⊆ A) hA_int
  -- Therefore `A` is open.
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))

theorem P1_iff_P2_iff_P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A ↔ P2 A ∧ P3 A := by
  constructor
  · intro _hP1
    exact ⟨P2_subsingleton (A := A), P3_subsingleton (A := A)⟩
  · intro _h
    exact P1_subsingleton (A := A)
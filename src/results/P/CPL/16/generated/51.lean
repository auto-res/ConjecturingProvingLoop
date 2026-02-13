

theorem P2_of_open_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro y hyImage
  -- Choose a preimage point `x`
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- From `P2 A` we have the required property for `x`
  have hxInt : (x : X) ∈ interior (closure (interior A)) := hP2 hxA
  -- Define the auxiliary open set `O`
  set O : Set Y := f '' interior (closure (interior A)) with hOdef
  have hO_open : IsOpen (O : Set Y) := by
    have hOpenSrc : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    simpa [hOdef] using hopen _ hOpenSrc
  -- Show  `O ⊆ closure (interior (f '' A))`
  have hO_subset : (O : Set Y) ⊆ closure (interior (f '' A)) := by
    intro z hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- First step:  `f x'` is in the closure of `f '' interior A`
    have h1 : (f x' : Y) ∈ closure (f '' interior A) := by
      -- Since `x' ∈ closure (interior A)`
      have hx'Cl : (x' : X) ∈ closure (interior A) :=
        interior_subset hx'Int
      -- Use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro V hV hVfx
      -- The preimage of `V` is open
      have hPreOpen : IsOpen (f ⁻¹' V) := hV.preimage hf
      have hx'Pre : x' ∈ f ⁻¹' V := by
        simpa using hVfx
      -- Intersect with `interior A`
      have hNonempty :
          ((f ⁻¹' V) ∩ interior A).Nonempty := by
        have := (mem_closure_iff).1 hx'Cl (f ⁻¹' V) hPreOpen hx'Pre
        simpa [Set.inter_comm] using this
      rcases hNonempty with ⟨x₁, hx₁Pre, hx₁IntA⟩
      exact
        ⟨f x₁, ⟨by
          simpa using hx₁Pre,
          ⟨x₁, hx₁IntA, rfl⟩⟩⟩
    -- Second step:  `closure (f '' interior A) ⊆ closure (interior (f '' A))`
    have hIncl :
        closure (f '' interior A : Set Y) ⊆
          closure (interior (f '' A)) := by
      -- Prove the basic inclusion `f '' interior A ⊆ interior (f '' A)`
      have h_img_subset :
          (f '' interior A : Set Y) ⊆ interior (f '' A) := by
        -- The image of an open set is open
        have hOpenImg : IsOpen (f '' interior A : Set Y) := by
          have hOpenSrc : IsOpen (interior A : Set X) := isOpen_interior
          simpa using hopen _ hOpenSrc
        -- And it is contained in `f '' A`
        have hSub : (f '' interior A : Set Y) ⊆ f '' A := by
          intro w hw
          rcases hw with ⟨x₂, hx₂Int, rfl⟩
          exact ⟨x₂, interior_subset hx₂Int, rfl⟩
        -- Apply `interior_maximal`
        exact interior_maximal hSub hOpenImg
      exact closure_mono h_img_subset
    exact hIncl h1
  -- Our original point belongs to `O`
  have hyO : (f x : Y) ∈ O := by
    dsimp [O] at hOdef
    simpa [hOdef] using ⟨x, hxInt, rfl⟩
  -- Conclude using `interior_maximal`
  have : (f x : Y) ∈ interior (closure (interior (f '' A))) :=
    (interior_maximal hO_subset hO_open) hyO
  exact this
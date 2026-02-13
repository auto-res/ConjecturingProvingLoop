

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : P1 (e '' A) := by
  -- Unfold the goal: we need `e '' A ⊆ closure (interior (e '' A))`.
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1 A` we have `x ∈ closure (interior A)`.
  have hx_closure : x ∈ closure (interior A) := hA hxA
  -- First show `e x ∈ closure (e '' interior A)`.
  have h1 : (e x) ∈ closure (e '' interior A) := by
    -- Use the characterization of closure via open neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro V hV hxV
    -- Consider the preimage of `V` under `e`.
    have h_pre_open : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
    have hx_pre : x ∈ e ⁻¹' V := by
      change e x ∈ V
      simpa using hxV
    -- Since `x` is in the closure of `interior A`, this intersection is non-empty.
    have h_nonempty : ((e ⁻¹' V) ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hx_closure _ h_pre_open hx_pre
    rcases h_nonempty with ⟨z, ⟨hzV, hzInt⟩⟩
    -- Map the witness forward with `e`.
    have hzV'   : e z ∈ V                := hzV
    have hzInt' : e z ∈ e '' interior A := ⟨z, hzInt, rfl⟩
    exact ⟨e z, ⟨hzV', hzInt'⟩⟩
  -- Next, show `e '' interior A ⊆ interior (e '' A)`.
  have h_subset : (e '' interior A : Set _) ⊆ interior (e '' A) := by
    -- It is an open subset of `e '' A`.
    have h_incl : (e '' interior A : Set _) ⊆ e '' A := by
      rintro y ⟨x, hxInt, rfl⟩
      exact ⟨x, interior_subset hxInt, rfl⟩
    have h_open : IsOpen (e '' interior A) := by
      simpa using e.isOpenMap.image (s := interior A) isOpen_interior
    exact interior_maximal h_incl h_open
  -- Taking closures preserves inclusion.
  have h_subset' : closure (e '' interior A) ⊆ closure (interior (e '' A)) :=
    closure_mono h_subset
  -- Finish.
  exact h_subset' h1

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  -- First, turn `hA` into `P1 A` and `P3 A`.
  have hP1A : P1 A := P1_of_P2 hA
  have hP3A : P3 A := P3_of_P2 hA
  -- Transport `P1` along the homeomorphism.
  have hP1Img : P1 (e '' A) := P1_image_homeomorph (e := e) hP1A
  -- We now prove `P3 (e '' A)`.
  have hP3Img : P3 (e '' A) := by
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    -- `x` lies in the interior of `closure A`.
    have hxInt : x ∈ interior (closure (A : Set X)) := hP3A hxA
    -- Show that `e x` belongs to the interior of the closure of `e '' A`.
    -- First, place it in an auxiliary open set.
    have hxImage : (e x) ∈ (e '' interior (closure (A : Set X))) :=
      ⟨x, hxInt, rfl⟩
    -- This open set sits inside `interior (closure (e '' A))`.
    have h_subset :
        (e '' interior (closure (A : Set X)) : Set Y) ⊆
          interior (closure (e '' (A : Set X))) := by
      -- Step 1: it is contained in `closure (e '' A)`.
      have h_incl :
          (e '' interior (closure (A : Set X)) : Set Y) ⊆
            closure (e '' (A : Set X)) := by
        rintro y ⟨x, hxInt', rfl⟩
        -- From `hxInt'` we know `x ∈ closure A`.
        have hx_closure : x ∈ closure (A : Set X) := interior_subset hxInt'
        -- Show `e x` is in the desired closure using the neighbourhood
        -- characterisation.
        have : (e x) ∈ closure (e '' (A : Set X)) := by
          refine (mem_closure_iff).2 ?_
          intro V hV hxV
          -- Pull back the open neighbourhood along `e`.
          have pre_open : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
          have hx_pre : x ∈ e ⁻¹' V := by
            change e x ∈ V
            simpa using hxV
          -- Use that `x ∈ closure A`.
          have h_ne : ((e ⁻¹' V) ∩ (A : Set X)).Nonempty :=
            (mem_closure_iff).1 hx_closure _ pre_open hx_pre
          rcases h_ne with ⟨z, ⟨hzV, hzA⟩⟩
          exact ⟨e z, ⟨hzV, ⟨z, hzA, rfl⟩⟩⟩
        exact this
      -- Step 2: the set is open because `e` is an open map.
      have h_open : IsOpen (e '' interior (closure (A : Set X))) := by
        simpa using
          e.isOpenMap.image (s := interior (closure (A : Set X))) isOpen_interior
      -- Conclude using the maximality property of interiors.
      exact interior_maximal h_incl h_open
    exact h_subset hxImage
  -- Combine `P1` and `P3` for the image, then use the characterisation of `P2`.
  exact (P2_iff_P1_P3).2 ⟨hP1Img, hP3Img⟩

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P3 A` we get that `x` lies in the interior of `closure A`.
  have hxInt : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Consider the image of this interior point.
  have hxImage : (e x) ∈ (e '' interior (closure (A : Set X))) :=
    ⟨x, hxInt, rfl⟩
  -- We show that the whole image of `interior (closure A)` sits inside
  -- `interior (closure (e '' A))`.
  have h_subset :
      (e '' interior (closure (A : Set X)) : Set Y) ⊆
        interior (closure (e '' (A : Set X))) := by
    -- First, prove containment in the closure.
    have h_incl :
        (e '' interior (closure (A : Set X)) : Set Y) ⊆
          closure (e '' (A : Set X)) := by
      rintro z ⟨x', hx', rfl⟩
      have hx'cl : (x' : X) ∈ closure (A : Set X) := interior_subset hx'
      -- Show that `e x'` is in the desired closure.
      have : (e x') ∈ closure (e '' (A : Set X)) := by
        refine (mem_closure_iff).2 ?_
        intro V hV hxV
        -- Pull back the neighbourhood along `e`.
        have hPreOpen : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
        have hxPre : x' ∈ e ⁻¹' V := by
          change e x' ∈ V
          simpa using hxV
        -- Use that `x' ∈ closure A`.
        have h_nonempty : ((e ⁻¹' V) ∩ (A : Set X)).Nonempty :=
          (mem_closure_iff).1 hx'cl _ hPreOpen hxPre
        rcases h_nonempty with ⟨t, ⟨htV, htA⟩⟩
        exact ⟨e t, ⟨htV, ⟨t, htA, rfl⟩⟩⟩
      simpa using this
    -- The image set is open because `e` is an open map.
    have h_open : IsOpen (e '' interior (closure (A : Set X))) := by
      simpa using
        e.isOpenMap.image (s := interior (closure (A : Set X))) isOpen_interior
    -- Apply maximality of the interior.
    exact interior_maximal h_incl h_open
  exact h_subset hxImage
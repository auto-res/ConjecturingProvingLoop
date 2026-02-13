

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P3 (A i) := h i
  have hx_int : x ∈ interior (closure (A i)) := hPi hxi
  have h_subset :
      (interior (closure (A i)) : Set X) ⊆ interior (closure (⋃ j, A j)) := by
    have subsetAi : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono (closure_mono subsetAi)
  exact h_subset hx_int

theorem P2_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  -- First, rewrite what we have to prove.
  -- We must show `e '' A ⊆ interior (closure (interior (e '' A)))`.
  intro y hy
  -- Obtain a preimage point in `A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use `hA` to know that `x` already satisfies `P2`.
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  -- Choose an open neighbourhood of `x` contained in `closure (interior A)`.
  rcases mem_interior.1 hx with ⟨U, hU_sub, hU_open, hxU⟩
  -- The image of an open set by a homeomorphism is open.
  have hU_im_open : IsOpen (e '' U) := (e.isOpenMap _ hU_open)
  -- `e x` is in that image.
  have hxy : (e x) ∈ e '' U := ⟨x, hxU, rfl⟩
  -- We show that this whole image is contained in the required closed set.
  have h_subset :
      (e '' U : Set Y) ⊆ closure (interior (e '' A)) := by
    -- Take an arbitrary point in `e '' U`.
    intro z hz
    rcases hz with ⟨u, huU, rfl⟩
    -- We will prove `e u` is in the closure of `interior (e '' A)`.
    have hu_cl : (u : X) ∈ closure (interior A) := hU_sub huU
    -- Use the neighbourhood characterisation of closure.
    have h_mem_cl :
        (∀ V : Set Y, IsOpen V → e u ∈ V → (V ∩ interior (e '' A)).Nonempty) := by
      intro V hV_open hV_mem
      -- Pull `V` back to an open set in `X`.
      have hV_pre_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
      have hV_pre_mem : u ∈ e ⁻¹' V := hV_mem
      -- By closure, the preimage intersects `interior A`.
      have h_nonempty :=
        ((mem_closure_iff).1 hu_cl) (e ⁻¹' V) hV_pre_open hV_pre_mem
      rcases h_nonempty with ⟨w, hw_pre, hw_int⟩
      -- `w ∈ interior A`, hence `e w ∈ e '' interior A`.
      have h_image_mem : (e w) ∈ e '' interior A := ⟨w, hw_int, rfl⟩
      -- The image of an open set is open; it is contained in `e '' A`,
      -- hence in its interior.
      have h_img_open : IsOpen (e '' interior A) :=
        (e.isOpenMap _ isOpen_interior)
      have h_img_subset : (e '' interior A : Set Y) ⊆ e '' A := by
        intro y hy
        rcases hy with ⟨t, ht, rfl⟩
        exact ⟨t, interior_subset ht, rfl⟩
      have h_img_int :
          (e w) ∈ interior (e '' A) := by
        -- `e '' interior A` is an open neighbourhood contained in `e '' A`.
        exact
          mem_interior.2
            ⟨e '' interior A, h_img_subset, h_img_open, h_image_mem⟩
      -- Finally, build the required non‐empty intersection.
      exact ⟨e w, by
        refine And.intro ?_ h_img_int
        simpa using hw_pre⟩
    -- Convert the neighbourhood criterion into the membership in the closure.
    exact (mem_closure_iff).2 h_mem_cl
  -- We have an open neighbourhood of `e x` contained in the desired closed set,
  -- hence `e x` belongs to the interior of that closed set.
  exact
    mem_interior.2
      ⟨e '' U, h_subset, hU_im_open, hxy⟩
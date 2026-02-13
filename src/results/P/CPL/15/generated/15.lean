

theorem P1_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the `P1` hypothesis on `A`
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- we show `e x` is in the required closure
  have : (e x) ∈ closure (interior (e '' A)) := by
    -- neighbourhood characterisation of closure
    refine (mem_closure_iff).2 ?_
    intro V hV_open hV_mem
    -- pull `V` back to `X`
    have hW_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
    have hW_mem : x ∈ e ⁻¹' V := by
      change e x ∈ V at hV_mem
      simpa [Set.mem_preimage] using hV_mem
    -- use that `x` is in the closure of `interior A`
    have h_nonempty :=
      (mem_closure_iff).1 hx_cl (e ⁻¹' V) hW_open hW_mem
    rcases h_nonempty with ⟨w, hwW, hw_intA⟩
    -- translate back to `Y`
    have hwV : e w ∈ V := by
      have : w ∈ e ⁻¹' V := hwW
      simpa [Set.mem_preimage] using this
    -- `e w` lies in the interior of `e '' A`
    have h_open_img : IsOpen (e '' interior A) :=
      (e.isOpenMap _ isOpen_interior)
    have h_img_subset : (e '' interior A : Set Y) ⊆ e '' A := by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact ⟨u, interior_subset hu, rfl⟩
    have hw_int : e w ∈ interior (e '' A) := by
      refine
        mem_interior.2
          ⟨e '' interior A, h_img_subset, h_open_img, ?_⟩
      exact ⟨w, hw_intA, rfl⟩
    exact ⟨e w, And.intro hwV hw_int⟩
  exact this

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  intro x hx
  -- First, prove that `closure A = univ`.
  have h_closure_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · -- `closure A ⊆ univ`
      intro y hy
      simp
    · -- `univ ⊆ closure A`, obtained from the assumption
      have h_subset : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [h] using h_subset
  -- Since `closure A = univ`, its interior is `univ`, hence the goal holds.
  simpa [h_closure_univ, interior_univ]
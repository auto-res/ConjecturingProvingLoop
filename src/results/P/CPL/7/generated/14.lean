

theorem open_iff_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · exact P3_of_P2
  · intro _hP3
    exact P2_of_open hA

theorem exists_closed_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ K, IsClosed K ∧ A ⊆ K ∧ closure K = closure A := by
  intro _
  refine ⟨closure (A : Set X), isClosed_closure, subset_closure, ?_⟩
  simpa [closure_closure]

theorem P1_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) (h : Homeomorph X Y) : P1 (h '' A) := by
  -- We must prove: `h '' A ⊆ closure (interior (h '' A))`.
  intro x hx
  -- Choose a preimage point `y : X` with `h y = x`.
  rcases hx with ⟨y, hyA, rfl⟩
  -- Using `P1 A`, `y` is in the closure of `interior A`.
  have hy_cl : y ∈ closure (interior (A : Set X)) := hA hyA
  -- We now show `h y ∈ closure (interior (h '' A))`.
  have : h y ∈ closure (interior (h '' A)) := by
    -- Use the neighbourhood formulation of the closure.
    apply (mem_closure_iff).2
    intro V hV_open hyV
    -- Pull back the neighbourhood under `h`.
    have hW_open : IsOpen (h ⁻¹' V) := hV_open.preimage h.continuous
    have hyW : y ∈ h ⁻¹' V := by
      simpa using hyV
    -- Since `y` is in the closure of `interior A`, `h ⁻¹' V` meets `interior A`.
    have h_nonempty :=
      (mem_closure_iff).1 hy_cl (h ⁻¹' V) hW_open hyW
    rcases h_nonempty with ⟨z, hzW, hz_intA⟩
    -- `hzW` gives `h z ∈ V`.
    have hzV : h z ∈ V := by
      simpa using hzW
    -- Show that `h z ∈ interior (h '' A)`.
    -- First, identify `h '' interior A` as a preimage by `h.symm` (hence open).
    have h_img_eq_preimage :
        (h '' interior A : Set _) = h.symm ⁻¹' interior A := by
      ext w
      constructor
      · rintro ⟨u, hu_int, rfl⟩
        simpa using hu_int
      · intro hw
        have : h.symm w ∈ interior A := hw
        exact
          ⟨h.symm w, this, by
            simpa using (h.apply_symm_apply w).symm⟩
    have hU_open : IsOpen (h '' interior A) := by
      have : IsOpen (h.symm ⁻¹' interior A) := by
        simpa using isOpen_interior.preimage h.symm.continuous
      simpa [h_img_eq_preimage] using this
    -- The image of `interior A` sits inside the image of `A`.
    have hU_subset : (h '' interior A : Set _) ⊆ h '' A := by
      rintro w ⟨u, hu_intA, rfl⟩
      exact ⟨u, interior_subset hu_intA, rfl⟩
    -- Hence `h '' interior A` is contained in the interior of `h '' A`.
    have hU_interior :
        (h '' interior A : Set _) ⊆ interior (h '' A) :=
      interior_maximal hU_subset hU_open
    -- Thus `h z` lies in that interior.
    have hz_int : h z ∈ interior (h '' A) := by
      have : h z ∈ (h '' interior A : Set _) := ⟨z, hz_intA, rfl⟩
      exact hU_interior this
    -- Produce a point in `V ∩ interior (h '' A)`.
    exact ⟨h z, And.intro hzV hz_int⟩
  exact this


theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A → P3 (f '' A) := (P3_homeomorph_iff (f := f) (A := A)).1

theorem P1_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P1 A → P1 (A ∩ B) := by
  intro hBopen hP1
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Use the neighbourhood characterization of the closure.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- `V ∩ B` is an open neighbourhood of `x`.
  have hVBopen : IsOpen (V ∩ B) := hVopen.inter hBopen
  have hxVB : x ∈ V ∩ B := ⟨hxV, hxB⟩
  -- From `P1 A`, we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Hence `(V ∩ B) ∩ interior A` is non-empty.
  have hNonempty : ((V ∩ B) ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_cl (V ∩ B) hVBopen hxVB
  rcases hNonempty with ⟨y, ⟨hyV, hyB⟩, hyIntA⟩
  -- Show that `y ∈ interior (A ∩ B)`.
  have hyIntAB : y ∈ interior (A ∩ B) := by
    -- `interior A ∩ B` is an open subset of `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) := by
      have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hBopen
      have hIncl : (interior A ∩ B : Set X) ⊆ A ∩ B := by
        intro z hz
        rcases hz with ⟨hzIntA, hzB⟩
        exact ⟨interior_subset hzIntA, hzB⟩
      exact interior_maximal hIncl hOpen
    exact hSub ⟨hyIntA, hyB⟩
  -- Provide the required intersection with the interior.
  exact ⟨y, hyV, hyIntAB⟩


theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A → P3 (e '' A) := by
  intro hP3
  intro y hy
  -- Choose a preimage point `x : X` with `y = e x`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the interior/closure condition.
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- The point `e x` lies in the image of this interior.
  have hmemImage : (e x : Y) ∈ (e '' interior (closure (A : Set X))) :=
    ⟨x, hx_int, rfl⟩
  ------------------------------------------------------------------
  -- 1.  The set `e '' interior (closure A)` is open.
  ------------------------------------------------------------------
  have h_open_image : IsOpen (e '' interior (closure (A : Set X))) := by
    --  It coincides with the preimage of an open set under `e.symm`.
    have h_equiv :
        (e '' interior (closure (A : Set X))) =
          (fun y : Y => e.symm y) ⁻¹' interior (closure (A : Set X)) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        simp [hx]
      · intro hy
        have hx : e.symm y ∈ interior (closure (A : Set X)) := hy
        exact ⟨e.symm y, hx, by simp⟩
    --  The right‐hand side is open by continuity of `e.symm`.
    have h_pre :
        IsOpen ((fun y : Y => e.symm y) ⁻¹' interior (closure (A : Set X))) := by
      exact isOpen_interior.preimage e.symm.continuous
    simpa [h_equiv] using h_pre
  ------------------------------------------------------------------
  -- 2.  This open image is contained in the interior of `e '' closure A`.
  ------------------------------------------------------------------
  have h_subset :
      (e '' interior (closure (A : Set X))) ⊆ interior (e '' closure (A : Set X)) := by
    apply interior_maximal
    · -- Inclusion into `e '' closure A`.
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, interior_subset hw, rfl⟩
    · exact h_open_image
  have hmemInt : (e x : Y) ∈ interior (e '' closure (A : Set X)) :=
    h_subset hmemImage
  ------------------------------------------------------------------
  -- 3.  Relate `e '' closure A` with `closure (e '' A)`.
  ------------------------------------------------------------------
  have h_closure_eq :
      (e '' closure (A : Set X)) = closure (e '' (A : Set X)) := by
    simpa using e.image_closure (A : Set X)
  --  Rewrite the goal using this equality.
  simpa [h_closure_eq] using hmemInt
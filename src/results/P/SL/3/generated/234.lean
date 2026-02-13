

theorem boundary_eq_closure_inter_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) =
      closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  classical
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- First inclusion: from left to right.
    intro x hx
    rcases hx with ⟨hx_clA, hx_notInt⟩
    -- `x` already belongs to `closure A`.
    have hx_clAc : (x : X) ∈ closure ((Aᶜ) : Set X) := by
      -- Use the identity `closure (Aᶜ) = (interior A)ᶜ`.
      have h_eq := closure_compl_eq_complement_interior (A := A)
      -- Since `x ∉ interior A`, we have `x ∈ (interior A)ᶜ`.
      have : (x : X) ∈ (interior (A : Set X))ᶜ := hx_notInt
      simpa [h_eq] using this
    exact And.intro hx_clA hx_clAc
  · -- Second inclusion: from right to left.
    intro x hx
    rcases hx with ⟨hx_clA, hx_clAc⟩
    -- Translate membership in `closure (Aᶜ)` to non-membership in `interior A`.
    have hx_notInt : (x : X) ∉ interior (A : Set X) := by
      -- Via `closure (Aᶜ) = (interior A)ᶜ`.
      have h_eq := closure_compl_eq_complement_interior (A := A)
      have : (x : X) ∈ (interior (A : Set X))ᶜ := by
        simpa [h_eq] using hx_clAc
      exact this
    exact And.intro hx_clA hx_notInt
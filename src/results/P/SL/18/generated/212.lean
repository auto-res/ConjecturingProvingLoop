

theorem interior_inter_subset_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `interior` is monotone with respect to set inclusion on the left factor.
  have hA :
      interior (A ∩ B : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  -- And similarly for the right factor.
  have hB :
      interior (A ∩ B : Set X) ⊆ interior B := by
    apply interior_mono
    exact Set.inter_subset_right
  -- Combine the two inclusions to obtain the desired membership.
  exact ⟨hA hx, hB hx⟩
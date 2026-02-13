

theorem Topology.closureInteriorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- First inclusion toward the `A` component.
  have hA : closure (interior (closure (A ∩ B)))
      ⊆ closure (interior (closure A)) := by
    apply closure_mono
    apply interior_mono
    -- `closure (A ∩ B)` is contained in `closure A`.
    have : (closure (A ∩ B) : Set X) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact this
  -- Second inclusion toward the `B` component.
  have hB : closure (interior (closure (A ∩ B)))
      ⊆ closure (interior (closure B)) := by
    apply closure_mono
    apply interior_mono
    -- `closure (A ∩ B)` is contained in `closure B`.
    have : (closure (A ∩ B) : Set X) ⊆ closure B := by
      apply closure_mono
      exact Set.inter_subset_right
    exact this
  exact ⟨hA hx, hB hx⟩
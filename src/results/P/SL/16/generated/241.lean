

theorem Topology.closure_inter_closed_left_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hClosed : IsClosed A) :
    closure (A ∩ B : Set X) ⊆ A ∩ closure B := by
  intro x hx
  have hxA : x ∈ A := by
    -- Since `A ∩ B ⊆ A`, taking closures gives
    -- `closure (A ∩ B) ⊆ closure A = A` (because `A` is closed).
    have h_subset : closure (A ∩ B : Set X) ⊆ A := by
      have h_temp : closure (A ∩ B : Set X) ⊆ closure A :=
        closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
      simpa [hClosed.closure_eq] using h_temp
    exact h_subset hx
  have hxB : x ∈ closure B := by
    -- Monotonicity of `closure` for the inclusion `A ∩ B ⊆ B`.
    have h_subset : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h_subset hx
  exact And.intro hxA hxB
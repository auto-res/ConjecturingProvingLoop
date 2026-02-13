

theorem Topology.closure_inter_closed_right_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hClosed : IsClosed B) :
    closure (A ∩ B : Set X) ⊆ closure A ∩ B := by
  intro x hx
  -- First, `x ∈ closure A` because `A ∩ B ⊆ A`.
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  -- Next, since `B` is closed and `A ∩ B ⊆ B`, we get `x ∈ B`.
  have hxB : x ∈ B := by
    have h_subset : closure (A ∩ B : Set X) ⊆ B := by
      -- Use the fact that `closure B = B` for a closed set `B`.
      have h_temp :
          closure (A ∩ B : Set X) ⊆ closure B :=
        closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
      simpa [hClosed.closure_eq] using h_temp
    exact h_subset hx
  exact And.intro hxA hxB
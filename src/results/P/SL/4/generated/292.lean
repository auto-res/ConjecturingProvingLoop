

theorem frontier_inter_subset_closure_pair
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- From `hx` we obtain membership in `closure (A ∩ B)`.
  have hx_cl : x ∈ closure (A ∩ B) := hx.1
  -- `closure (A ∩ B)` is contained in each of `closure A` and `closure B`.
  have hA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact And.intro (hA hx_cl) (hB hx_cl)
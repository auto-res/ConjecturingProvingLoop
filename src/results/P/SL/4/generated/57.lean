

theorem closure_interior_inter_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono (interior_mono Set.inter_subset_left)
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono (interior_mono Set.inter_subset_right)
  exact And.intro (hA hx) (hB hx)
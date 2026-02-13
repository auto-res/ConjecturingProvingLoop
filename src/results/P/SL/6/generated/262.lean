

theorem closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Inclusion into `closure A`.
  have hA : closure ((A ∩ interior B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  -- Inclusion into `closure B`.
  have hB : closure ((A ∩ interior B) : Set X) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact (interior_subset : interior B ⊆ B) hy.2
  exact And.intro (hA hx) (hB hx)
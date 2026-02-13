

theorem closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure ((A ∩ B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hB : closure ((A ∩ B) : Set X) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact hy.2
  exact And.intro (hA hx) (hB hx)
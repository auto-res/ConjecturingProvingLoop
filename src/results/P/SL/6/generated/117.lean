

theorem closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X))
      ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Inclusion into `closure (interior A)`
  have hA :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact hy.1
  -- Inclusion into `closure (interior B)`
  have hB :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact hy.2
  exact And.intro (hA hx) (hB hx)
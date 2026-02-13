

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ B ⊆ A` and `A ∩ B ⊆ B`
  have hSubA : ((A ∩ B) : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  have hSubB : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  -- Taking closures preserves inclusions.
  have hClA : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) :=
    closure_mono hSubA
  have hClB : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) :=
    closure_mono hSubB
  exact And.intro (hClA hx) (hClB hx)
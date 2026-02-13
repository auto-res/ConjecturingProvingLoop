

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior A ∩ interior B) : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in each of `interior A`, `interior B`.
  have hSubA : (interior A ∩ interior B : Set X) ⊆ interior A := by
    intro y hy; exact hy.1
  have hSubB : (interior A ∩ interior B : Set X) ⊆ interior B := by
    intro y hy; exact hy.2
  -- Taking closures preserves inclusions.
  have hClA :
      closure ((interior A ∩ interior B) : Set X) ⊆ closure (interior A) :=
    closure_mono hSubA
  have hClB :
      closure ((interior A ∩ interior B) : Set X) ⊆ closure (interior B) :=
    closure_mono hSubB
  exact And.intro (hClA hx) (hClB hx)
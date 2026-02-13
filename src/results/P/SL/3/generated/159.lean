

theorem closure_inter_interiors_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B` is contained in `interior A`
  have hA_sub : interior (A : Set X) ∩ interior B ⊆ interior A := by
    intro y hy
    exact hy.1
  -- `interior A ∩ interior B` is contained in `interior B`
  have hB_sub : interior (A : Set X) ∩ interior B ⊆ interior B := by
    intro y hy
    exact hy.2
  -- Hence, their closures satisfy the desired inclusions
  have hxA : (x : X) ∈ closure (interior A) := (closure_mono hA_sub) hx
  have hxB : (x : X) ∈ closure (interior B) := (closure_mono hB_sub) hx
  exact And.intro hxA hxB
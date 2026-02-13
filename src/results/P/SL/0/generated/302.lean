

theorem closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X) ∩ interior (B : Set X)) : Set X) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- The set `interior A ∩ interior B` is contained in `interior A`.
  have hSubA :
      ((interior (A : Set X)) ∩ interior (B : Set X) : Set X) ⊆
        interior (A : Set X) := by
    intro y hy; exact hy.1
  have hxA : x ∈ closure (interior (A : Set X)) :=
    (closure_mono hSubA) hx
  -- Likewise, it is contained in `interior B`.
  have hSubB :
      ((interior (A : Set X)) ∩ interior (B : Set X) : Set X) ⊆
        interior (B : Set X) := by
    intro y hy; exact hy.2
  have hxB : x ∈ closure (interior (B : Set X)) :=
    (closure_mono hSubB) hx
  exact And.intro hxA hxB
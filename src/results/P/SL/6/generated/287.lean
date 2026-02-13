

theorem interior_closure_inter_closures_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` sits inside each factor.
  have hSubA :
      closure ((A : Set X)) ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  have hSubB :
      closure ((A : Set X)) ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Apply monotonicity of `interior` to obtain the two memberships.
  have hxA : x ∈ interior (closure A) :=
    (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono hSubB) hx
  exact And.intro hxA hxB
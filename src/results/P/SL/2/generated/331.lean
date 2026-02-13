

theorem Topology.interior_inter_closures_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in each of `closure A` and `closure B`.
  have hSubA :
      (closure (A : Set X) ∩ closure (B : Set X) : Set X) ⊆ closure (A : Set X) :=
    by
      intro y hy
      exact hy.1
  have hSubB :
      (closure (A : Set X) ∩ closure (B : Set X) : Set X) ⊆ closure (B : Set X) :=
    by
      intro y hy
      exact hy.2
  -- Apply monotonicity of `interior` to both inclusions.
  have hIntA :
      interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
        interior (closure (A : Set X)) :=
    interior_mono hSubA
  have hIntB :
      interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
        interior (closure (B : Set X)) :=
    interior_mono hSubB
  exact And.intro (hIntA hx) (hIntB hx)
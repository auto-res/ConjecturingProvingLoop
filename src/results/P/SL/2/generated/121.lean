

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Step 1: relate `closure (A ∩ B)` to `closure A` and `closure B`
  have hclA : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
    have hsub : ((A ∩ B) : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact closure_mono hsub
  have hclB : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
    have hsub : ((A ∩ B) : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact closure_mono hsub
  -- Step 2: use monotonicity of `interior` to obtain the desired memberships
  have hxA : x ∈ interior (closure (A : Set X)) :=
    (interior_mono hclA) hx
  have hxB : x ∈ interior (closure (B : Set X)) :=
    (interior_mono hclB) hx
  exact And.intro hxA hxB
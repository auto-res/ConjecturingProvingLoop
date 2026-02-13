

theorem Topology.interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in each individual closure.
  have hA : closure (A ∩ B) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hB : closure (A ∩ B) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact hy.2
  -- Use monotonicity of `interior` to upgrade the membership.
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono hB) hx
  exact And.intro hxA hxB
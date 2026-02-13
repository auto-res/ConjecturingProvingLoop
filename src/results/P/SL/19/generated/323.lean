

theorem Topology.interior_closure_inter_mono_left
    {X : Type*} [TopologicalSpace X] {A B C : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (A ∩ C)) ⊆ interior (closure (B ∩ C)) := by
  intro x hx
  -- First, upgrade the inclusion `(A ∩ C) ⊆ (B ∩ C)` to closures.
  have hClos : closure (A ∩ C) ⊆ closure (B ∩ C) := by
    have hSub : (A ∩ C : Set X) ⊆ B ∩ C := by
      intro y hy
      exact And.intro (hAB hy.1) hy.2
    exact closure_mono hSub
  -- Then apply monotonicity of `interior` to conclude.
  exact (interior_mono hClos) hx
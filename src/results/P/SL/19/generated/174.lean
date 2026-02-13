

theorem Topology.closure_inter_mono_left {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (A ∩ C) ⊆ closure (B ∩ C) := by
  have hSub : (A ∩ C : Set X) ⊆ B ∩ C := by
    intro x hx
    exact And.intro (hAB hx.1) hx.2
  exact closure_mono hSub
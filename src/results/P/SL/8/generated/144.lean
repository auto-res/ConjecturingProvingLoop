

theorem closure_subset_closureInterior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    closure A ⊆ closure (interior B) := by
  -- First, use monotonicity of `closure` to enlarge from `A` to `B`.
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  -- Unfold the definition of `P1` for `B`.
  dsimp [Topology.P1] at hP1B
  -- Since `closure (interior B)` is closed and contains `B`,
  -- minimality of the closure yields the desired inclusion.
  have h₂ : closure B ⊆ closure (interior B) :=
    closure_minimal hP1B isClosed_closure
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂
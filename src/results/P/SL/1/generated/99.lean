

theorem Topology.P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → B ⊆ interior (closure (interior A)) → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  -- A handy inclusion used in both cases.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- First, `interior A ⊆ interior (A ∪ B)`.
    have h₁ : interior A ⊆ interior (A ∪ B) := by
      apply interior_mono
      intro y hy
      exact Or.inl hy
    -- Then take closures.
    have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h₁
    -- Finally, take interiors once more.
    exact interior_mono h₂
  -- Split on whether `x` comes from `A` or `B`.
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure (interior A)) := hA hxA
      exact hsubset hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure (interior A)) := hB hxB
      exact hsubset hxInt
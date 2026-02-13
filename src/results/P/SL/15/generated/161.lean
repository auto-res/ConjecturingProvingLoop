

theorem P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hP1A ⊢
  intro x hx_union
  -- We need to show that `x` belongs to `closure (interior (A ∪ B))`.
  -- First, note that `interior A ⊆ interior (A ∪ B)`.
  have hIntSubset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
    exact interior_mono h_sub
  -- Consequently, taking closures preserves the inclusion.
  have hClosMono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hIntSubset
  -- Now treat the two possible ways in which `x` can lie in `A ∪ B`.
  cases hx_union with
  | inl hxA =>
      -- Case `x ∈ A`: use `P1` for `A`.
      have hx_clA : x ∈ closure (interior A) := hP1A hxA
      exact hClosMono hx_clA
  | inr hxB =>
      -- Case `x ∈ B`: use the assumption `B ⊆ closure (interior A)`.
      have hx_clA : x ∈ closure (interior A) := hBsubset hxB
      exact hClosMono hx_clA
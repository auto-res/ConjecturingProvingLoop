

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- Unfold `P2` for the given hypotheses and the goal.
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  -- Analyse the membership of `x` in the union.
  cases hx with
  | inl hxA =>
      -- `x` satisfies the `P2` condition for `A`.
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show that the relevant neighbourhoods for `A`
      -- are contained in those for `A ∪ B`.
      have h_sub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior A ⊆ interior (A ∪ B)`.
        have h1 : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        -- Step 2: take closures.
        have h2 : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        -- Step 3: take interiors again.
        exact interior_mono h2
      exact h_sub hxA'
  | inr hxB =>
      -- Symmetric argument for the `B` branch.
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have h_sub : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h1 : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        have h2 : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact h_sub hxB'
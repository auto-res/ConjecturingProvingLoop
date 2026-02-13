

theorem Topology.closureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C)) := by
  intro x hx
  -- Split the triple union into two cases.
  rcases hx with hxAB | hxC
  · -- Case `x ∈ closure (interior A) ∪ closure (interior B)`.
    -- First, use the two–set lemma to upgrade the target set.
    have hxAB' :
        (x : X) ∈ closure (interior (A ∪ B)) :=
      (Topology.closureInterior_union_subset (X := X) (A := A) (B := B)) hxAB
    -- Next, enlarge from `A ∪ B` to `A ∪ B ∪ C` via monotonicity.
    have h_incl :
        closure (interior (A ∪ B)) ⊆
          closure (interior (A ∪ B ∪ C)) := by
      have h_subset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inl hy
      exact
        Topology.closureInterior_mono
          (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) h_subset
    exact h_incl hxAB'
  · -- Case `x ∈ closure (interior C)`.
    have h_subset : (C : Set X) ⊆ A ∪ B ∪ C := by
      intro y hy
      exact Or.inr hy
    have h_incl :
        closure (interior C) ⊆
          closure (interior (A ∪ B ∪ C)) :=
      Topology.closureInterior_mono
        (X := X) (A := C) (B := A ∪ B ∪ C) h_subset
    exact h_incl hxC
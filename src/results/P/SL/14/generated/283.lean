

theorem Topology.union_interior_three_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior A ∪ interior B ∪ interior C : Set X) ⊆
      interior (A ∪ B ∪ C) := by
  -- We first handle the two–set case `A ∪ B`.
  have h₁ :
      (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A) (B := B)
  -- Next, we enlarge to include `C`.
  have h₂ :
      (interior (A ∪ B) ∪ interior C : Set X) ⊆
        interior ((A ∪ B) ∪ C) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A ∪ B) (B := C)
  -- Now take an arbitrary point in the triple union.
  intro x hx
  -- The expression `interior A ∪ interior B ∪ interior C` is parsed as
  -- `(interior A ∪ interior B) ∪ interior C`, so we can case–split.
  cases hx with
  | inl hAB =>
      -- `x` lies in `interior A ∪ interior B`
      have hxAB : (x : X) ∈ interior (A ∪ B) := h₁ hAB
      -- Hence `x` lies in `interior (A ∪ B) ∪ interior C`
      have hx₁ : (x : X) ∈ (interior (A ∪ B) ∪ interior C : Set X) :=
        Or.inl hxAB
      -- Apply the second inclusion.
      exact h₂ hx₁
  | inr hC =>
      -- `x` lies in the `interior C` branch.
      have hx₂ : (x : X) ∈ (interior (A ∪ B) ∪ interior C : Set X) :=
        Or.inr hC
      exact h₂ hx₂
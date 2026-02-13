

theorem boundary_union_subset_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∪ B) : Set X) \ interior ((A ∪ B) : Set X) ⊆
      (closure (A : Set X) \ interior (A : Set X)) ∪
        (closure (B : Set X) \ interior (B : Set X)) := by
  intro x hx
  rcases hx with ⟨hxClUnion, hxNotIntUnion⟩
  -- Use the description of `closure (A ∪ B)` as the union of the closures.
  have hClEq : closure ((A ∪ B) : Set X) =
      closure (A : Set X) ∪ closure (B : Set X) :=
    closure_union_eq_union_closure (A := A) (B := B)
  have hxCl : (x : X) ∈ closure (A : Set X) ∪ closure (B : Set X) := by
    simpa [hClEq] using hxClUnion
  -- Show that `x` is not in the interior of `A` nor in that of `B`.
  have hxNotIntA : (x : X) ∉ interior (A : Set X) := by
    intro hxIntA
    have hSubset : (A : Set X) ⊆ (A ∪ B) := by
      intro y hy; exact Or.inl hy
    have hxIntUnion :
        (x : X) ∈ interior ((A ∪ B) : Set X) :=
      (interior_mono hSubset) hxIntA
    exact hxNotIntUnion hxIntUnion
  have hxNotIntB : (x : X) ∉ interior (B : Set X) := by
    intro hxIntB
    have hSubset : (B : Set X) ⊆ (A ∪ B) := by
      intro y hy; exact Or.inr hy
    have hxIntUnion :
        (x : X) ∈ interior ((A ∪ B) : Set X) :=
      (interior_mono hSubset) hxIntB
    exact hxNotIntUnion hxIntUnion
  -- Finally, place `x` in the appropriate boundary.
  cases hxCl with
  | inl hxClA =>
      exact Or.inl ⟨hxClA, hxNotIntA⟩
  | inr hxClB =>
      exact Or.inr ⟨hxClB, hxNotIntB⟩
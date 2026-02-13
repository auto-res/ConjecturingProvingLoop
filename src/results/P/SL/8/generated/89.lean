

theorem closureInterior_inter_subset_inter_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : interior (A ∩ B) ⊆ interior A := by
    have : A ∩ B ⊆ A := Set.inter_subset_left
    exact interior_mono this
  have hB : interior (A ∩ B) ⊆ interior B := by
    have : A ∩ B ⊆ B := Set.inter_subset_right
    exact interior_mono this
  -- Take closures to relate the membership of `x`
  have hxA : x ∈ closure (interior A) := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB
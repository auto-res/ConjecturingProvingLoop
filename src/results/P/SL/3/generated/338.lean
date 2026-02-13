

theorem closure_interior_inter_subset_inter_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X) ∩ B) : Set X) ⊆
      closure (interior (A : Set X)) ∩ closure (B : Set X) := by
  intro x hx
  -- `interior A ∩ B` is contained in both `interior A` and `B`
  have hA : (interior (A : Set X) ∩ B : Set X) ⊆ interior (A : Set X) := by
    intro y hy; exact hy.1
  have hB : (interior (A : Set X) ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy; exact hy.2
  -- Hence, the closure of `interior A ∩ B` is contained in the closures of
  -- `interior A` and `B`, respectively.
  have hxA : (x : X) ∈ closure (interior (A : Set X)) :=
    (closure_mono hA) hx
  have hxB : (x : X) ∈ closure (B : Set X) :=
    (closure_mono hB) hx
  exact And.intro hxA hxB
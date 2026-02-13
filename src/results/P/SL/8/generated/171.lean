

theorem closureInterior_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure A ∩ closure B := by
  -- First, use the existing inclusion into the intersection of
  -- the closures of the interiors.
  have h₁ :
      closure (interior (A ∩ B)) ⊆
        closure (interior A) ∩ closure (interior B) :=
    closureInterior_inter_subset_inter_closureInterior
      (X := X) (A := A) (B := B)
  -- Next, observe that each `closure (interior _)` is contained in the corresponding `closure _`.
  have h₂ :
      (closure (interior A) ∩ closure (interior B)) ⊆
        closure A ∩ closure B := by
    intro x hx
    rcases hx with ⟨hxA, hxB⟩
    exact And.intro
      (closure_interior_subset_closure (X := X) (A := A) hxA)
      (closure_interior_subset_closure (X := X) (A := B) hxB)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂
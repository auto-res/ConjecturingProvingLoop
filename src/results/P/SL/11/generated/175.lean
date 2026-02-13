

theorem P1_of_P1_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (h : Topology.P1 (A ×ˢ B)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at h ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  -- Form the point in the product set.
  have hxy : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Use `P1` for the product to obtain closure membership.
  have hcl₁ : (x, y) ∈ closure (interior (A ×ˢ B)) := h hxy
  -- Rewrite the interior of a product as the product of interiors.
  have hcl₂ :
      (x, y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [interior_prod_eq] using hcl₁
  -- Rewrite the closure of a product as the product of closures.
  have hcl₃ :
      (x, y) ∈ closure (interior A) ×ˢ closure (interior B) := by
    simpa [closure_prod_eq] using hcl₂
  -- Extract the first coordinate to conclude.
  exact hcl₃.1
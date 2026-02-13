

theorem P2_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P2 A := by
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxA
  rcases hB with ⟨y, hyB⟩
  -- Form the point in the product set.
  have hxy_prod : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product.
  have hmem : (x, y) ∈ interior (closure (interior (A ×ˢ B))) :=
    hP2 hxy_prod
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hmem₁ :
      (x, y) ∈ interior (closure ((interior A) ×ˢ (interior B))) := by
    simpa [interior_prod_eq] using hmem
  -- Use the lemma `interior_closure_prod_eq` to split the closure of a product.
  have hmem₂ :
      (x, y) ∈ interior (closure (interior A) ×ˢ closure (interior B)) := by
    simpa [interior_closure_prod_eq
            (A := interior A) (B := interior B)] using hmem₁
  -- Apply `interior_prod_eq` once more to separate the coordinates.
  have hmem₃ :
      (x, y) ∈ interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
    simpa [interior_prod_eq] using hmem₂
  -- Extract the first coordinate to conclude `P2` for `A`.
  exact hmem₃.1
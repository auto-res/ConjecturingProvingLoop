

theorem P2_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P2 B := by
  dsimp [Topology.P2] at hP2 ⊢
  intro y hyB
  rcases hA with ⟨x, hxA⟩
  -- Form the point `(x, y) ∈ A ×ˢ B`.
  have hxy : (x, y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
  -- Apply `P2` for the product.
  have hxy_int : (x, y) ∈ interior (closure (interior (A ×ˢ B))) := hP2 hxy
  -- Rewrite `interior (A ×ˢ B)` via `interior_prod_eq`.
  have hxy_int₁ :
      (x, y) ∈ interior (closure ((interior A) ×ˢ (interior B))) := by
    simpa [interior_prod_eq] using hxy_int
  -- Use the lemma `interior_closure_prod_eq` to split the closure of a product.
  have hxy_int₂ :
      (x, y) ∈ interior (closure (interior A) ×ˢ closure (interior B)) := by
    simpa [interior_closure_prod_eq
            (A := interior A) (B := interior B)] using hxy_int₁
  -- Apply `interior_prod_eq` once more to separate the coordinates.
  have hxy_int₃ :
      (x, y) ∈ interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
    simpa [interior_prod_eq] using hxy_int₂
  -- Extract the second coordinate to conclude `P2` for `B`.
  exact hxy_int₃.2
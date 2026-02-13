

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  -- First, merge `A` and `B`.
  have hAB : P1 (A ∪ B) := P1_union hA hB
  -- Then, merge the result with `C`.
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (A ∪ B ∪ C ∪ D) := by
  have hABC : P2 (A ∪ B ∪ C) := P2_union_three hA hB hC
  have hABCD : P2 ((A ∪ B ∪ C) ∪ D) := P2_union hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.image (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2)) (A ×ˢ B ×ˢ C)) := by
  -- Unpack the image membership: obtain a pre-image point in the product set.
  intro xyz hxyz
  rcases hxyz with ⟨xyz0, hmem0, rfl⟩
  -- Decompose the triple point into its three coordinates.
  rcases xyz0 with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  -- `hmem0` gives component-wise membership in the product set `A ×ˢ B ×ˢ C`.
  rcases hmem0 with ⟨hxA, hyzBC⟩
  rcases hyzBC with ⟨hyB, hzC⟩
  -- Apply the `P1` hypotheses to each coordinate separately.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  have hz_cl : z ∈ closure (interior C) := hC hzC
  ------------------------------------------------------------------
  -- Step 1: treat the `(y , z)` block.
  ------------------------------------------------------------------
  have h_BC_cl : (y, z) ∈ closure (interior (B ×ˢ C)) := by
    -- First place `(y , z)` in the product of the closures,
    -- then rewrite with the product rules for `closure` and `interior`.
    have hprod : (y, z) ∈ closure (interior B) ×ˢ closure (interior C) :=
      ⟨hy_cl, hz_cl⟩
    simpa [closure_prod_eq, interior_prod_eq] using hprod
  ------------------------------------------------------------------
  -- Step 2: assemble the three coordinates.
  ------------------------------------------------------------------
  have h_xyz_cl : (x, (y, z)) ∈ closure (interior (A ×ˢ B ×ˢ C)) := by
    -- Again use the product rules, now for the outer product.
    have hprod :
        (x, (y, z)) ∈ closure (interior A) ×ˢ
          closure (interior (B ×ˢ C)) := by
      exact ⟨hx_cl, h_BC_cl⟩
    simpa [closure_prod_eq, interior_prod_eq] using hprod
  ------------------------------------------------------------------
  -- Step 3: upgrade to the required set (the image),
  --         using monotonicity of `interior` and `closure`.
  ------------------------------------------------------------------
  -- The product set is contained in its image under the (essentially
  -- identity) map, hence the same is true for the corresponding
  -- closures of interiors.
  have hsub :
      (A ×ˢ B ×ˢ C : Set (X × Y × Z)) ⊆
        Set.image
          (fun xyz : X × Y × Z =>
            (xyz.1, (xyz.2).1, (xyz.2).2))
          (A ×ˢ B ×ˢ C) := by
    intro xyz' hxyz'
    exact ⟨xyz', hxyz', rfl⟩
  have hsubset_cl :
      closure (interior (A ×ˢ B ×ˢ C)) ⊆
        closure (interior (Set.image
          (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2))
          (A ×ˢ B ×ˢ C))) :=
    closure_mono (interior_mono hsub)
  ------------------------------------------------------------------
  -- Step 4: conclude.
  ------------------------------------------------------------------
  exact hsubset_cl h_xyz_cl
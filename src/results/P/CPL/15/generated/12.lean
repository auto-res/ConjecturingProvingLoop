

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P2 (A i) := h i
  have hx_int : x ∈ interior (closure (interior (A i))) := hPi hxi
  have h_subset :
      (interior (closure (interior (A i))) : Set X) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    have subsetAi : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono (closure_mono (interior_mono subsetAi))
  exact h_subset hx_int

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  -- Decompose the point `p` into its two coordinates.
  rcases p with ⟨x, y⟩
  -- Extract componentwise membership from `hp`.
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P3` hypotheses to each component.
  have hx_int : x ∈ interior (closure A) := hA hxA
  have hy_int : y ∈ interior (closure B) := hB hyB
  -- Choose open neighbourhoods of `x` and `y` contained in the respective closures.
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  rcases mem_interior.1 hy_int with ⟨V, hV_sub, hV_open, hyV⟩
  -- The product of these neighbourhoods is an open neighbourhood of `(x, y)`.
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : ((x, y) : X × Y) ∈ U ×ˢ V := by
    exact And.intro hxU hyV
  -- Show that this neighbourhood is contained in `closure (A ×ˢ B)`.
  have hUV_sub : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro z hz
    -- First, it is contained in `closure A ×ˢ closure B`.
    have hz_prod : z ∈ closure A ×ˢ closure B :=
      (Set.prod_mono hU_sub hV_sub) hz
    -- Identify this product with the closure of the product.
    simpa [closure_prod_eq] using hz_prod
  -- Conclude that `(x, y)` belongs to the required interior.
  exact
    mem_interior.2 ⟨U ×ˢ V, hUV_sub, hUV_open, hpUV⟩